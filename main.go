package main

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"crypto/tls"
	"database/sql"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

const PortaGo = ":80"

var (
	dbUsers         *sql.DB
	dbMerger        *sql.DB
	httpClient      *http.Client
	clientAcelerado *http.Client
	streamClient    *http.Client
	CacheLock       sync.RWMutex
)

const (
	arquivoIPsClientes   = "ips_clientes.txt"
	arquivoIPsBloqueados = "ips_bloqueados.txt"
)

var (
	ipsRegistrados     = make(map[string]bool)
	ipsRegistradosLock sync.RWMutex
	ipsBloqueados      = make(map[string]bool)
	ipsBloqueadosLock  sync.RWMutex
	ipsBloqueadosMod   time.Time
)

type CatEntry struct {
	NomeOriginal string
	NomeNovo     string
	Ordem        int
}

type FonteConfig struct {
	ID   int
	Host string
	User string
	Pass string
	Tipo string
}

func (f FonteConfig) ServeLive() bool { return f.Tipo == "both" || f.Tipo == "live" }
func (f FonteConfig) ServeVod() bool  { return f.Tipo == "both" || f.Tipo == "vod" }

type EnvConfig struct {
	FormatoCanal string
	SigmaPaineis []string
	Fontes         []FonteConfig
	AtualizarHoras int
	AdminUser string
	AdminPass string
	AdminDNS  string
	MergerPainelUser string
	MergerPainelPass string
	FiltroSemAdultos  map[string][]string
	OrdemCanais       map[string]CatEntry
	OrdemFilmes       map[string]CatEntry
	OrdemSeries       map[string]CatEntry
	OcultaTodosCanais []string
	OcultaTodosFilmes []string
	OcultaTodosSeries []string
	WebPlayers []string
}

var Env EnvConfig

var (
	ApiCache        = make(map[string][]byte)
	M3UCache        []byte
	fonteRouter     = make(map[int]FonteConfig)
	fonteRouterLock sync.RWMutex
)

func getFontePorID(fonteID int) (FonteConfig, bool) {
	fonteRouterLock.RLock()
	defer fonteRouterLock.RUnlock()
	f, ok := fonteRouter[fonteID]
	return f, ok
}

var bufPool = sync.Pool{
	New: func() interface{} {
		buf := make([]byte, 128*1024)
		return &buf
	},
}

type AuthEntry struct {
	ExpDate  int64
	MaxCons  int
	Bouquet  string
	Valido   bool
	CachedAt time.Time
}

var (
	authCache     = make(map[string]AuthEntry)
	authCacheLock sync.RWMutex
	authCacheTTL  = 30 * time.Second
)

func validarUsuarioCache(user, pass string) (int64, int, string, bool) {
	if user == "" || pass == "" { return 0, 0, "", false }
	chave := user + ":" + pass
	authCacheLock.RLock()
	entry, ok := authCache[chave]
	authCacheLock.RUnlock()
	if ok && time.Since(entry.CachedAt) < authCacheTTL {
		return entry.ExpDate, entry.MaxCons, entry.Bouquet, entry.Valido
	}
	expDate, maxCons, bouquet, valido := validarUsuarioSQLite(user, pass)
	authCacheLock.Lock()
	authCache[chave] = AuthEntry{ExpDate: expDate, MaxCons: maxCons, Bouquet: bouquet, Valido: valido, CachedAt: time.Now()}
	authCacheLock.Unlock()
	return expDate, maxCons, bouquet, valido
}

func limparAuthCache() {
	for {
		time.Sleep(60 * time.Second)
		authCacheLock.Lock()
		agora := time.Now()
		for k, v := range authCache {
			if agora.Sub(v.CachedAt) > authCacheTTL*2 { delete(authCache, k) }
		}
		authCacheLock.Unlock()
	}
}

func invalidarAuthCache() {
	authCacheLock.Lock()
	authCache = make(map[string]AuthEntry)
	authCacheLock.Unlock()
}

type IPEntry struct {
	IP        string
	UltimoUso time.Time
}

var (
	ipTracker     = make(map[string][]IPEntry)
	ipTrackerLock sync.RWMutex
	ipTTL         = 30 * time.Minute
)

func pegarIP(r *http.Request) string {
	if cf := r.Header.Get("CF-Connecting-IP"); cf != "" { return strings.TrimSpace(cf) }
	if xff := r.Header.Get("X-Forwarded-For"); xff != "" { return strings.TrimSpace(strings.Split(xff, ",")[0]) }
	if xri := r.Header.Get("X-Real-Ip"); xri != "" { return xri }
	ip := r.RemoteAddr
	if idx := strings.LastIndex(ip, ":"); idx != -1 { ip = ip[:idx] }
	return ip
}

func verificarIP(username, ip string, maxCons int) (bool, int, int) {
	ipTrackerLock.Lock()
	defer ipTrackerLock.Unlock()
	agora := time.Now()
	ips := ipTracker[username]
	var ativos []IPEntry
	for _, entry := range ips {
		if agora.Sub(entry.UltimoUso) < ipTTL { ativos = append(ativos, entry) }
	}
	encontrado := false
	for i, entry := range ativos {
		if entry.IP == ip {
			ativos[i].UltimoUso = agora
			encontrado = true
			break
		}
	}
	if !encontrado {
		if len(ativos) >= maxCons { return false, len(ativos), maxCons }
		ativos = append(ativos, IPEntry{IP: ip, UltimoUso: agora})
	}
	ipTracker[username] = ativos
	return true, len(ativos), maxCons
}

func limparIPsExpirados() {
	for {
		time.Sleep(30 * time.Minute)
		ipTrackerLock.Lock()
		agora := time.Now()
		for user, ips := range ipTracker {
			var ativos []IPEntry
			for _, entry := range ips {
				if agora.Sub(entry.UltimoUso) < ipTTL { ativos = append(ativos, entry) }
			}
			if len(ativos) == 0 { delete(ipTracker, user) } else { ipTracker[user] = ativos }
		}
		ipTrackerLock.Unlock()
	}
}

func getConexoesAtivas() (int, []map[string]string) {
	ipTrackerLock.RLock()
	defer ipTrackerLock.RUnlock()
	agora := time.Now()
	total := 0
	var lista []map[string]string
	for user, ips := range ipTracker {
		for _, entry := range ips {
			if agora.Sub(entry.UltimoUso) < ipTTL {
				total++
				lista = append(lista, map[string]string{"username": user, "ip": entry.IP, "expira": entry.UltimoUso.Add(ipTTL).Format("15:04:05")})
			}
		}
	}
	return total, lista
}

func carregarIPsRegistrados() {
	ipsRegistradosLock.Lock()
	defer ipsRegistradosLock.Unlock()
	data, err := os.ReadFile(arquivoIPsClientes)
	if err != nil { return }
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" { continue }
		partes := strings.SplitN(line, ",", 2)
		if len(partes) >= 1 {
			ip := strings.TrimSpace(partes[0])
			ip = strings.Trim(ip, `"`)
			if ip != "" { ipsRegistrados[ip] = true }
		}
	}
}

func carregarIPsBloqueados() {
	ipsBloqueadosLock.Lock()
	defer ipsBloqueadosLock.Unlock()
	info, err := os.Stat(arquivoIPsBloqueados)
	if err != nil {
		os.WriteFile(arquivoIPsBloqueados, []byte(""), 0644)
		ipsBloqueados = make(map[string]bool)
		return
	}
	if info.ModTime().Equal(ipsBloqueadosMod) { return }
	ipsBloqueadosMod = info.ModTime()
	data, err := os.ReadFile(arquivoIPsBloqueados)
	if err != nil { return }
	novo := make(map[string]bool)
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		ip := strings.TrimSpace(line)
		if ip != "" && !strings.HasPrefix(ip, "#") { novo[ip] = true }
	}
	ipsBloqueados = novo
}

func ipBloqueado(ip string) bool {
	ipsBloqueadosLock.RLock()
	defer ipsBloqueadosLock.RUnlock()
	return ipsBloqueados[ip]
}

func resolverOperadora(ip string) string {
	nomes, err := net.LookupAddr(ip)
	if err != nil || len(nomes) == 0 { return "Desconhecida" }
	nome := strings.TrimSuffix(nomes[0], ".")
	partes := strings.Split(nome, ".")
	if len(partes) >= 3 { return strings.Join(partes[len(partes)-3:], ".") }
	return nome
}

func registrarIPCliente(ip, username, userAgent string) {
	ipsRegistradosLock.RLock()
	jaExiste := ipsRegistrados[ip]
	ipsRegistradosLock.RUnlock()
	if jaExiste { return }
	ipsRegistradosLock.Lock()
	if ipsRegistrados[ip] { ipsRegistradosLock.Unlock(); return }
	ipsRegistrados[ip] = true
	ipsRegistradosLock.Unlock()
	operadora := resolverOperadora(ip)
	userAgent = strings.ReplaceAll(userAgent, `"`, "'")
	linha := fmt.Sprintf(`"%s", "%s", "%s", "%s"`, ip, username, userAgent, operadora)
	f, err := os.OpenFile(arquivoIPsClientes, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err == nil { f.WriteString(linha + "\n"); f.Close() }
}

func monitorarIPsBloqueados() {
	for { time.Sleep(10 * time.Second); carregarIPsBloqueados() }
}

var gzipWriterPool = sync.Pool{
	New: func() interface{} { w, _ := gzip.NewWriterLevel(nil, gzip.BestSpeed); return w },
}

func setCORS(w http.ResponseWriter) {
	w.Header().Set("Access-Control-Allow-Origin", "*")
	w.Header().Set("Access-Control-Allow-Methods", "GET, POST, OPTIONS, PUT, DELETE")
	w.Header().Set("Access-Control-Allow-Headers", "*")
	w.Header().Set("Access-Control-Max-Age", "86400")
}

func escreverResposta(w http.ResponseWriter, r *http.Request, contentType string, dados []byte) {
	setCORS(w)
	w.Header().Set("Content-Type", contentType)
	w.Header().Set("Connection", "keep-alive")
	aceitaGzip := r != nil && strings.Contains(r.Header.Get("Accept-Encoding"), "gzip")
	if len(dados) > 1024 && aceitaGzip {
		w.Header().Set("Content-Encoding", "gzip")
		gz := gzipWriterPool.Get().(*gzip.Writer)
		gz.Reset(w)
		gz.Write(dados)
		gz.Close()
		gzipWriterPool.Put(gz)
	} else { w.Write(dados) }
}

func isIPAddress(s string) bool { return net.ParseIP(s) != nil }
func isWebPlayer(ip string) bool {
	for _, wp := range Env.WebPlayers { if ip == wp { return true } }
	return false
}
func isAppAntigo(ua string) bool {
	ua = strings.ToLower(ua)
	antigos := []string{"smart stb", "smart-stb", "ss iptv", "gse", "perfect player", "lazy iptv", "kodi", "vlc"}
	for _, a := range antigos { if strings.Contains(ua, a) { return true } }
	return false
}

func iniciarBancoUsuarios() {
	var err error
	dbUsers, err = sql.Open("sqlite3", "./usuarios.db?_journal_mode=WAL&_busy_timeout=5000&cache=shared")
	if err != nil { log.Fatal("❌ Erro SQLite usuarios.db:", err) }
	dbUsers.SetMaxOpenConns(10)
	dbUsers.SetMaxIdleConns(5)
	dbUsers.SetConnMaxLifetime(5 * time.Minute)
	query := `CREATE TABLE IF NOT EXISTS clientes (id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE NOT NULL, password TEXT NOT NULL, exp_date INTEGER NOT NULL, max_connections INTEGER DEFAULT 1, bouquet TEXT, created_at INTEGER, painel TEXT DEFAULT '', enabled INTEGER DEFAULT 1, admin_notes TEXT DEFAULT '', reseller_notes TEXT DEFAULT '', is_trial INTEGER DEFAULT 0);
	CREATE INDEX IF NOT EXISTS idx_username ON clientes(username); CREATE INDEX IF NOT EXISTS idx_painel ON clientes(painel);`
	dbUsers.Exec(query)
	dbUsers.Exec("ALTER TABLE clientes ADD COLUMN painel TEXT DEFAULT ''")
	dbUsers.Exec("ALTER TABLE clientes ADD COLUMN enabled INTEGER DEFAULT 1")
	dbUsers.Exec("ALTER TABLE clientes ADD COLUMN admin_notes TEXT DEFAULT ''")
	dbUsers.Exec("ALTER TABLE clientes ADD COLUMN reseller_notes TEXT DEFAULT ''")
	dbUsers.Exec("ALTER TABLE clientes ADD COLUMN is_trial INTEGER DEFAULT 0")
	fmt.Println("✅ usuarios.db Ativado")
}

func iniciarBancoMerger() {
	var err error
	dbMerger, err = sql.Open("sqlite3", "./merger.db?_journal_mode=WAL&_busy_timeout=5000&cache=shared")
	if err != nil { log.Fatal("❌ Erro SQLite merger.db:", err) }
	dbMerger.SetMaxOpenConns(5); dbMerger.SetMaxIdleConns(3)
	dbMerger.Exec(`CREATE TABLE IF NOT EXISTS stream_direto (fonte_id INTEGER NOT NULL, stream_id_original TEXT NOT NULL, tipo TEXT NOT NULL, PRIMARY KEY(fonte_id,stream_id_original,tipo));`)
	dbMerger.Exec(`CREATE TABLE IF NOT EXISTS canal_24h (fonte_id INTEGER NOT NULL, stream_id_original TEXT NOT NULL, tipo TEXT NOT NULL, PRIMARY KEY(fonte_id,stream_id_original,tipo));`)
	dbMerger.Exec(`CREATE TABLE IF NOT EXISTS categorias (id INTEGER PRIMARY KEY AUTOINCREMENT,virtual_id TEXT NOT NULL,nome_original TEXT,nome_final TEXT NOT NULL,tipo TEXT NOT NULL,ordem INTEGER DEFAULT 99999,merge_key TEXT NOT NULL,UNIQUE(merge_key,tipo));
CREATE TABLE IF NOT EXISTS cat_map (fonte_id INTEGER NOT NULL,cat_id_original TEXT NOT NULL,virtual_cat_id TEXT NOT NULL,tipo TEXT NOT NULL,PRIMARY KEY(fonte_id,cat_id_original,tipo));
CREATE TABLE IF NOT EXISTS streams (id INTEGER PRIMARY KEY AUTOINCREMENT,fonte_id INTEGER NOT NULL,stream_id_original TEXT NOT NULL,virtual_stream_id TEXT NOT NULL,virtual_cat_id TEXT NOT NULL,tipo TEXT NOT NULL,json_data TEXT NOT NULL,UNIQUE(fonte_id,stream_id_original,tipo));
CREATE TABLE IF NOT EXISTS bloqueados (fonte_id INTEGER NOT NULL,stream_id_original TEXT NOT NULL,tipo TEXT NOT NULL,PRIMARY KEY(fonte_id,stream_id_original,tipo));
CREATE TABLE IF NOT EXISTS bloqueados_cat (virtual_id TEXT NOT NULL,tipo TEXT NOT NULL,PRIMARY KEY(virtual_id,tipo));
CREATE TABLE IF NOT EXISTS icon_overrides (fonte_id INTEGER NOT NULL,stream_id_original TEXT NOT NULL,tipo TEXT NOT NULL,novo_icon TEXT NOT NULL,PRIMARY KEY(fonte_id,stream_id_original,tipo));
CREATE TABLE IF NOT EXISTS name_overrides (fonte_id INTEGER NOT NULL,stream_id_original TEXT NOT NULL,tipo TEXT NOT NULL,novo_nome TEXT NOT NULL,PRIMARY KEY(fonte_id,stream_id_original,tipo));
CREATE TABLE IF NOT EXISTS url_overrides (fonte_id INTEGER NOT NULL,stream_id_original TEXT NOT NULL,tipo TEXT NOT NULL,novo_url TEXT NOT NULL,PRIMARY KEY(fonte_id,stream_id_original,tipo));
CREATE INDEX IF NOT EXISTS idx_streams_tipo ON streams(tipo);CREATE INDEX IF NOT EXISTS idx_cat_map ON cat_map(fonte_id,cat_id_original);`)
	fmt.Println("✅ merger.db Ativado")
}

func validarUsuarioSQLite(user, pass string) (int64, int, string, bool) {
	if user == "" || pass == "" { return 0, 0, "", false }
	var dbPass, dbBouquet string; var expDate int64; var maxCons, enabled int
	err := dbUsers.QueryRow("SELECT password, exp_date, max_connections, bouquet, COALESCE(enabled, 1) FROM clientes WHERE username = ?", user).Scan(&dbPass, &expDate, &maxCons, &dbBouquet, &enabled)
	if err == nil && dbPass == pass {
		if enabled == 0 { return 0, 0, "", false }
		if expDate > 0 && expDate < time.Now().Unix() { return 0, 0, "", false }
		maxCons = maxCons + 1
		return expDate, maxCons, dbBouquet, true
	}
	return 0, 0, "", false
}

func parseExpDate(raw string) int64 {
	raw = strings.TrimSpace(raw); if raw == "" || raw == "0" { return 0 }
	if ts, err := strconv.ParseInt(raw, 10, 64); err == nil && ts > 1000000000 { return ts }
	formatos := []string{"2006-01-02T15:04:05", "2006-01-02 15:04:05", "2006-01-02T15:04", "2006-01-02 15:04", "2006-01-02", "02/01/2006 15:04:05", "02/01/2006"}
	for _, formato := range formatos {
		if t, err := time.ParseInLocation(formato, raw, time.Local); err == nil { return t.Unix() }
	}
	return 0
}

func carregarEnv() {
	Env.FormatoCanal = ".ts"; Env.AtualizarHoras = 24; Env.FiltroSemAdultos = make(map[string][]string); Env.OrdemCanais = make(map[string]CatEntry); Env.OrdemFilmes = make(map[string]CatEntry); Env.OrdemSeries = make(map[string]CatEntry); Env.MergerPainelUser = "admin"; Env.MergerPainelPass = "admin"
	data, err := os.ReadFile(".env")
	if err != nil { Env.SigmaPaineis = []string{"GoMaIn123"}; return }
	lines := strings.Split(string(data), "\n"); secao := ""; ordemIdx := 0; fontesMap := make(map[int]*FonteConfig)
	for _, rawLine := range lines {
		line := strings.TrimSpace(rawLine); if line == "" || strings.HasPrefix(line, "========") { continue }
		lineUpper := strings.ToUpper(line)
		if strings.HasPrefix(lineUpper, "SIGMA") && strings.Contains(line, "=") {
			partes := strings.SplitN(line, "=", 2)
			if len(partes) == 2 {
				for _, item := range strings.Split(partes[1], ",") { item = strings.TrimSpace(item); if item != "" { Env.SigmaPaineis = append(Env.SigmaPaineis, item) } }
			}
			continue
		}
		if strings.HasPrefix(lineUpper, "FORMAT_CANAL") || strings.HasPrefix(lineUpper, "FORMAT CANAL") {
			if p := strings.SplitN(line, "=", 2); len(p) == 2 { v := strings.TrimSpace(p[1]); if !strings.HasPrefix(v, ".") { v = "." + v }; Env.FormatoCanal = v }
			continue
		}
		if strings.HasPrefix(lineUpper, "ADMIN_USER") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { Env.AdminUser = strings.TrimSpace(p[1]) }; continue }
		if strings.HasPrefix(lineUpper, "ADMIN_PASS") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { Env.AdminPass = strings.TrimSpace(p[1]) }; continue }
		if strings.HasPrefix(lineUpper, "ADMIN_DNS") || strings.HasPrefix(lineUpper, "DNS") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { Env.AdminDNS = strings.TrimSpace(p[1]) }; continue }
		if strings.HasPrefix(lineUpper, "MERGER_PAINEL_USER") || strings.HasPrefix(lineUpper, "PAINEL_USER") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { Env.MergerPainelUser = strings.TrimSpace(p[1]) }; continue }
		if strings.HasPrefix(lineUpper, "MERGER_PAINEL_PASS") || strings.HasPrefix(lineUpper, "PAINEL_PASS") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { Env.MergerPainelPass = strings.TrimSpace(p[1]) }; continue }
		if strings.HasPrefix(lineUpper, "ATUALIZAR_HORAS") { if p := strings.SplitN(line, "=", 2); len(p) == 2 { if h, e := strconv.Atoi(strings.TrimSpace(p[1])); e == nil && h >= 1 { Env.AtualizarHoras = h } }; continue }
		if strings.HasPrefix(lineUpper, "WEBPLAYER") {
			if p := strings.SplitN(line, "=", 2); len(p) == 2 {
				for _, item := range strings.Split(p[1], ",") {
					item = strings.TrimSpace(item); if item == "" { continue }
					if !strings.Contains(item, ":") && !isIPAddress(item) { ips, err := net.LookupHost(item); if err == nil { for _, ip := range ips { Env.WebPlayers = append(Env.WebPlayers, ip) } }; Env.WebPlayers = append(Env.WebPlayers, item) } else { Env.WebPlayers = append(Env.WebPlayers, item) }
				}
			}
			continue
		}
		if strings.HasPrefix(lineUpper, "FONTE_") {
			partes := strings.SplitN(line, "=", 2); if len(partes) != 2 { continue }; chave := strings.TrimSpace(strings.ToUpper(partes[0])); valor := strings.TrimSpace(partes[1])
			parts := strings.SplitN(chave[len("FONTE_"):], "_", 2); if len(parts) != 2 { continue }; idx, err := strconv.Atoi(parts[0]); if err != nil || idx < 1 { continue }
			if fontesMap[idx] == nil { fontesMap[idx] = &FonteConfig{ID: idx, Tipo: "both"} }
			switch parts[1] {
			case "HOST": fontesMap[idx].Host = valor
			case "USER": fontesMap[idx].User = valor
			case "PASS": fontesMap[idx].Pass = valor
			case "TIPO", "TYPE": t := strings.ToLower(valor); if t == "live" || t == "vod" || t == "both" { fontesMap[idx].Tipo = t }
			}
			continue
		}
		if lineUpper == "COMPLETO S/ ADULTOS" { secao = "FILTRO_ADULTOS"; continue }
		if lineUpper == "OCULTA PARA TODOS" { secao = "OCULTA"; continue }
		if lineUpper == "CANAIS" && !strings.Contains(line, "=") { secao = "ORDEM_CANAIS"; ordemIdx = 0; continue }
		if lineUpper == "FILMES" && !strings.Contains(line, "=") { secao = "ORDEM_FILMES"; ordemIdx = 0; continue }
		if lineUpper == "SERIES" && !strings.Contains(line, "=") { secao = "ORDEM_SERIES"; ordemIdx = 0; continue }
		switch secao {
		case "FILTRO_ADULTOS": if p := strings.SplitN(line, "=", 2); len(p) == 2 { t := strings.TrimSpace(strings.ToUpper(p[0])); for _, item := range strings.Split(p[1], ",") { item = strings.TrimSpace(strings.Trim(strings.TrimSpace(item), `"`)); if item != "" { Env.FiltroSemAdultos[t] = append(Env.FiltroSemAdultos[t], strings.ToUpper(item)) } } }
		case "ORDEM_CANAIS": entry := parseCatLine(line, ordemIdx); Env.OrdemCanais[strings.ToUpper(entry.NomeOriginal)] = entry; ordemIdx++
		case "ORDEM_FILMES": entry := parseCatLine(line, ordemIdx); Env.OrdemFilmes[strings.ToUpper(entry.NomeOriginal)] = entry; ordemIdx++
		case "ORDEM_SERIES": entry := parseCatLine(line, ordemIdx); Env.OrdemSeries[strings.ToUpper(entry.NomeOriginal)] = entry; ordemIdx++
		case "OCULTA": if p := strings.SplitN(line, "=", 2); len(p) == 2 { t := strings.TrimSpace(strings.ToUpper(p[0])); for _, item := range strings.Split(p[1], ",") { item = strings.TrimSpace(strings.Trim(strings.TrimSpace(item), `"`)); if item == "" { continue }; switch t { case "CANAIS": Env.OcultaTodosCanais = append(Env.OcultaTodosCanais, strings.ToUpper(item)); case "FILMES": Env.OcultaTodosFilmes = append(Env.OcultaTodosFilmes, strings.ToUpper(item)); case "SERIES": Env.OcultaTodosSeries = append(Env.OcultaTodosSeries, strings.ToUpper(item)) } } }
		}
	}
	var indices []int
	for idx := range fontesMap { indices = append(indices, idx) }
	sort.Ints(indices)
	for _, idx := range indices { f := fontesMap[idx]; if f.Host != "" && f.User != "" { Env.Fontes = append(Env.Fontes, *f) } }
	if len(Env.SigmaPaineis) == 0 { Env.SigmaPaineis = []string{"GoMaIn123"} }
	if Env.AdminUser == "" { Env.AdminUser = "admin" }
	if Env.AdminPass == "" { Env.AdminPass = "admin123" }
}

func parseCatLine(line string, ordem int) CatEntry {
	if idx := strings.Index(line, "="); idx != -1 { return CatEntry{NomeOriginal: strings.TrimSpace(line[:idx]), NomeNovo: strings.TrimSpace(line[idx+1:]), Ordem: ordem} }
	return CatEntry{NomeOriginal: line, NomeNovo: line, Ordem: ordem}
}

func getCatInfo(catName, tipoConteudo string) (string, int) {
	nameUpper := strings.ToUpper(catName); var mapa map[string]CatEntry
	switch tipoConteudo { case "live": mapa = Env.OrdemCanais; case "movie", "vod": mapa = Env.OrdemFilmes; case "series": mapa = Env.OrdemSeries }
	if entry, ok := mapa[nameUpper]; ok { return entry.NomeNovo, entry.Ordem }
	for chave, entry := range mapa { if strings.Contains(nameUpper, chave) || strings.Contains(chave, nameUpper) { return entry.NomeNovo, entry.Ordem } }
	return catName, 99999
}

func isOcultaParaTodos(catName, tipoConteudo string) bool {
	nameUpper := strings.ToUpper(catName); var lista []string
	switch tipoConteudo { case "live": lista = Env.OcultaTodosCanais; case "movie", "vod": lista = Env.OcultaTodosFilmes; case "series": lista = Env.OcultaTodosSeries }
	for _, oculta := range lista { if nameUpper == oculta || strings.Contains(nameUpper, oculta) || strings.Contains(oculta, nameUpper) { return true } }
	return false
}

func isFiltradaSemAdultos(catName, tipoConteudo string) bool {
	nameUpper := strings.ToUpper(catName); var chave string
	switch tipoConteudo { case "live": chave = "CANAIS"; case "movie", "vod": chave = "FILMES"; case "series": chave = "SERIES" }
	for _, filtrada := range Env.FiltroSemAdultos[chave] { if nameUpper == filtrada || strings.Contains(nameUpper, filtrada) || strings.Contains(filtrada, nameUpper) { return true } }
	return false
}

func extrairIDSeguro(val interface{}) string {
	switch v := val.(type) { case float64: return strconv.FormatFloat(v, 'f', -1, 64); case string: return v; default: return fmt.Sprintf("%v", val) }
}
func gerarVirtualStreamID(fonteID int, originalID string) string { return fmt.Sprintf("%03d%s", fonteID, originalID) }
func parseVirtualID(s string) (int, string, bool) {
	if len(s) <= 3 { return 0, s, false }; fID, err := strconv.Atoi(s[:3]); if err != nil || fID < 1 { return 0, s, false }; orig := s[3:]; if orig == "" { return 0, s, false }; return fID, orig, true
}
func limparURLsFonte(rawStr string, fonte FonteConfig) string {
	rawStr = strings.ReplaceAll(rawStr, fonte.Host+":80", "{HOST}"); rawStr = strings.ReplaceAll(rawStr, fonte.Host, "{HOST}"); rawStr = strings.ReplaceAll(rawStr, `\/\/`+fonte.Host, `\/\/{HOST}`); rawStr = strings.ReplaceAll(rawStr, fonte.User, "{USER}"); rawStr = strings.ReplaceAll(rawStr, fonte.Pass, "{PASS}")
	for _, pref := range []string{"http://", `http:\/\/`, "https://", `https:\/\/`} { rawStr = trocarHostDesconhecido(rawStr, pref) }
	return rawStr
}
func trocarHostDesconhecido(rawStr, prefixo string) string {
	resultado := rawStr; offset := 0
	for {
		idx := strings.Index(resultado[offset:], prefixo); if idx == -1 { break }; pos := offset + idx + len(prefixo); if pos >= len(resultado) { break }; if strings.HasPrefix(resultado[pos:], "{HOST}") { offset = pos + 6; continue }
		hostFim := pos
		for hostFim < len(resultado) { c := resultado[hostFim]; if c == '/' || c == '"' || c == '\'' || c == ' ' || c == '\n' { break }; if c == '\\' && hostFim+1 < len(resultado) && resultado[hostFim+1] == '/' { break }; hostFim++ }
		if hostFim == pos { offset = hostFim + 1; continue }; host := resultado[pos:hostFim]; restFim := hostFim
		for restFim < len(resultado) { c := resultado[restFim]; if c == '"' || c == '\'' || c == ' ' || c == '\n' { break }; restFim++ }
		restoURL := resultado[hostFim:restFim]
		if strings.Contains(restoURL, "{USER}") { resultado = resultado[:pos] + "{HOST}" + resultado[pos+len(host):]; offset = pos + 6 } else { offset = hostFim }
	}
	return resultado
}
func substituir(dados []byte, user, pass, host string) []byte { return []byte(strings.NewReplacer("{USER}", user, "{PASS}", pass, "{HOST}", host).Replace(string(dados))) }
func marshalJSON(v interface{}) []byte { var buf bytes.Buffer; enc := json.NewEncoder(&buf); enc.SetEscapeHTML(false); enc.Encode(v); return bytes.TrimSpace(buf.Bytes()) }
func virtualizarEpisodios(data []byte, fonteID int) []byte {
	dec := json.NewDecoder(bytes.NewReader(data)); dec.UseNumber(); var info map[string]interface{}; if dec.Decode(&info) != nil { return data }
	episodes, ok := info["episodes"]; if !ok { return data }; seasonsMap, ok := episodes.(map[string]interface{}); if !ok { return data }
	for season, epList := range seasonsMap {
		eps, ok := epList.([]interface{}); if !ok { continue }
		for i, ep := range eps { epMap, ok := ep.(map[string]interface{}); if !ok { continue }; if rawID, exists := epMap["id"]; exists && rawID != nil { idStr := fmt.Sprintf("%v", rawID); if idStr != "" && idStr != "<nil>" { epMap["id"] = gerarVirtualStreamID(fonteID, idStr) } }; eps[i] = epMap }
		seasonsMap[season] = eps
	}
	info["episodes"] = seasonsMap; var buf bytes.Buffer; enc := json.NewEncoder(&buf); enc.SetEscapeHTML(false); enc.Encode(info); return bytes.TrimSpace(buf.Bytes())
}
func linkExpoeCredenciais(link string) bool {
	for _, f := range Env.Fontes { if f.User != "" && strings.Contains(link, f.User) { return true }; if f.Pass != "" && strings.Contains(link, f.Pass) { return true } }
	return false
}

func atualizarTudo() {
	fmt.Println("🔄 [MERGER] Atualizando fontes...")
	inicio := time.Now()
	fonteRouterLock.Lock(); fonteRouter = make(map[int]FonteConfig); for _, f := range Env.Fontes { fonteRouter[f.ID] = f }; fonteRouterLock.Unlock()
	dbMerger.Exec("DELETE FROM categorias"); dbMerger.Exec("DELETE FROM cat_map"); dbMerger.Exec("DELETE FROM streams")
	processarCategorias("get_live_categories", "live"); processarCategorias("get_vod_categories", "movie"); processarCategorias("get_series_categories", "series")
	processarStreams("get_live_streams", "live"); processarStreams("get_vod_streams", "movie"); processarStreams("get_series", "series")
	montarCacheJSON()
	CacheLock.Lock(); M3UCache = montarM3U(); CacheLock.Unlock()
	fmt.Printf("✅ [MERGER] Pronto em %s | M3U: %.2f MB\n", time.Since(inicio).Round(time.Second), float64(len(M3UCache))/(1024*1024))
}
func processarCategorias(action, tipoConteudo string) {
	contadorCat := 100000; dbMerger.QueryRow("SELECT COALESCE(MAX(CAST(virtual_id AS INTEGER)),100000) FROM categorias").Scan(&contadorCat)
	for _, fonte := range Env.Fontes {
		if tipoConteudo == "live" && !fonte.ServeLive() { continue }; if (tipoConteudo == "movie" || tipoConteudo == "series") && !fonte.ServeVod() { continue }
		apiURL := fmt.Sprintf("http://%s/player_api.php?username=%s&password=%s&action=%s", fonte.Host, fonte.User, fonte.Pass, action)
		req, _ := http.NewRequest("GET", apiURL, nil); req.Header.Set("User-Agent", "IPTV Smarters Pro"); resp, err := httpClient.Do(req); if err != nil { continue }
		raw, _ := io.ReadAll(resp.Body); resp.Body.Close(); rawStr := limparURLsFonte(string(raw), fonte)
		var dados []map[string]interface{}; if json.Unmarshal([]byte(rawStr), &dados) != nil { continue }
		for _, item := range dados {
			catName, _ := item["category_name"].(string); catIDOriginal := extrairIDSeguro(item["category_id"]); if isOcultaParaTodos(catName, tipoConteudo) { continue }
			novoNome, ordem := getCatInfo(catName, tipoConteudo); mergeKey := strings.ToUpper(novoNome); var virtualID string
			err := dbMerger.QueryRow("SELECT virtual_id FROM categorias WHERE merge_key=? AND tipo=?", mergeKey, tipoConteudo).Scan(&virtualID)
			if err != nil { contadorCat++; virtualID = strconv.Itoa(contadorCat); dbMerger.Exec("INSERT OR IGNORE INTO categorias(virtual_id,nome_original,nome_final,tipo,ordem,merge_key) VALUES(?,?,?,?,?,?)", virtualID, catName, novoNome, tipoConteudo, ordem, mergeKey) }
			dbMerger.Exec("INSERT OR REPLACE INTO cat_map(fonte_id,cat_id_original,virtual_cat_id,tipo) VALUES(?,?,?,?)", fonte.ID, catIDOriginal, virtualID, tipoConteudo)
		}
	}
}
func processarStreams(action, tipoConteudo string) {
	for _, fonte := range Env.Fontes {
		if tipoConteudo == "live" && !fonte.ServeLive() { continue }; if (tipoConteudo == "movie" || tipoConteudo == "series") && !fonte.ServeVod() { continue }
		apiURL := fmt.Sprintf("http://%s/player_api.php?username=%s&password=%s&action=%s", fonte.Host, fonte.User, fonte.Pass, action)
		req, _ := http.NewRequest("GET", apiURL, nil); req.Header.Set("User-Agent", "IPTV Smarters Pro"); resp, err := httpClient.Do(req); if err != nil { continue }
		raw, _ := io.ReadAll(resp.Body); resp.Body.Close(); rawStr := limparURLsFonte(string(raw), fonte)
		var items []json.RawMessage; if json.Unmarshal([]byte(rawStr), &items) != nil { continue }
		tx, _ := dbMerger.Begin(); stmt, _ := tx.Prepare("INSERT OR REPLACE INTO streams(fonte_id,stream_id_original,virtual_stream_id,virtual_cat_id,tipo,json_data) VALUES(?,?,?,?,?,?)")
		for _, rawItem := range items {
			var peek map[string]interface{}; if json.Unmarshal(rawItem, &peek) != nil { continue }
			catIDOrig := extrairIDSeguro(peek["category_id"]); if idx := strings.Index(catIDOrig, ","); idx != -1 { catIDOrig = catIDOrig[:idx] }
			streamIDOrig := extrairIDSeguro(peek["stream_id"]); if streamIDOrig == "" || streamIDOrig == "<nil>" { streamIDOrig = extrairIDSeguro(peek["series_id"]) }
			vStream := gerarVirtualStreamID(fonte.ID, streamIDOrig); var vCat string
			err := dbMerger.QueryRow("SELECT virtual_cat_id FROM cat_map WHERE fonte_id=? AND cat_id_original=? AND tipo=?", fonte.ID, catIDOrig, tipoConteudo).Scan(&vCat); if err != nil { vCat = catIDOrig }
			peek["category_id"] = vCat; if vCatInt, errConv := strconv.Atoi(vCat); errConv == nil { peek["category_ids"] = []interface{}{float64(vCatInt)} }
			if peek["stream_id"] != nil { peek["stream_id"] = vStream; peek["num"] = vStream }; if peek["series_id"] != nil { peek["series_id"] = vStream }
			stmt.Exec(fonte.ID, streamIDOrig, vStream, vCat, tipoConteudo, string(marshalJSON(peek)))
		}
		stmt.Close(); tx.Commit()
	}
}
func montarCacheJSON() {
	CacheLock.Lock(); defer CacheLock.Unlock()
	for _, c := range []struct{ a, t string }{{"get_live_categories", "live"}, {"get_vod_categories", "movie"}, {"get_series_categories", "series"}} {
		rows, err := dbMerger.Query("SELECT virtual_id,nome_final FROM categorias WHERE tipo=? AND NOT EXISTS(SELECT 1 FROM bloqueados_cat bc WHERE bc.virtual_id=categorias.virtual_id AND bc.tipo=categorias.tipo) ORDER BY ordem ASC", c.t)
		if err != nil { ApiCache[c.a] = []byte("[]"); continue }; var buf bytes.Buffer; buf.WriteByte('['); first := true
		for rows.Next() { var vid, nome string; rows.Scan(&vid, &nome); if !first { buf.WriteByte(',') }; fmt.Fprintf(&buf, `{"category_id":"%s","category_name":"%s","parent_id":0}`, vid, nome); first = false }; rows.Close(); buf.WriteByte(']'); ApiCache[c.a] = buf.Bytes()
	}
	for _, c := range []struct{ a, t string }{{"get_live_streams", "live"}, {"get_vod_streams", "movie"}, {"get_series", "series"}} {
		rows, err := dbMerger.Query(`SELECT s.json_data, s.fonte_id, s.stream_id_original FROM streams s WHERE s.tipo=? AND NOT EXISTS(SELECT 1 FROM bloqueados b WHERE b.fonte_id=s.fonte_id AND b.stream_id_original=s.stream_id_original AND b.tipo=s.tipo) AND NOT EXISTS(SELECT 1 FROM bloqueados_cat bc WHERE bc.virtual_id=s.virtual_cat_id AND bc.tipo=s.tipo)`, c.t)
		if err != nil { ApiCache[c.a] = []byte("[]"); continue }; var buf bytes.Buffer; buf.WriteByte('['); first := true
		for rows.Next() {
			var j string; var fid int; var sid string; rows.Scan(&j, &fid, &sid); var novoIcon, novoNome string
			dbMerger.QueryRow("SELECT novo_icon FROM icon_overrides WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fid, sid, c.t).Scan(&novoIcon)
			dbMerger.QueryRow("SELECT novo_nome FROM name_overrides WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fid, sid, c.t).Scan(&novoNome)
			if novoIcon != "" || novoNome != "" { var peek map[string]interface{}; if json.Unmarshal([]byte(j), &peek) == nil { if novoIcon != "" { peek["stream_icon"] = novoIcon }; if novoNome != "" { peek["name"] = novoNome }; j = string(marshalJSON(peek)) } }
			if !first { buf.WriteByte(',') }; buf.WriteString(j); first = false
		}; rows.Close(); buf.WriteByte(']'); ApiCache[c.a] = buf.Bytes()
	}
}

type M3UEntry struct { InfoLine string; URLLine string; Group string; Ordem int }
func extrairGroupTitle(line string) string { idx := strings.Index(line, `group-title="`); if idx == -1 { return "" }; inicio := idx + len(`group-title="`); fim := strings.Index(line[inicio:], `"`); if fim == -1 { return "" }; return line[inicio : inicio+fim] }
func renomearGroupTitle(line, velho, novo string) string { return strings.Replace(line, `group-title="`+velho+`"`, `group-title="`+novo+`"`, 1) }
func formatarURLM3U(line string, fonteID int) string {
	partes := strings.Split(line, "/"); if len(partes) < 4 { return line }; arquivo := partes[len(partes)-1]; id, ext := arquivo, ""
	if idx := strings.LastIndex(arquivo, "."); idx != -1 { id, ext = arquivo[:idx], strings.ToLower(arquivo[idx:]) }
	pasta := "live"; if strings.Contains(line, "/movie/") { pasta = "movie" } else if strings.Contains(line, "/series/") { pasta = "series" }
	vID := gerarVirtualStreamID(fonteID, id)
	if pasta == "live" { return fmt.Sprintf("http://{HOST}/%s/{USER}/{PASS}/%s{EXT_LIVE}", pasta, vID) }
	if ext == "" || (ext != ".mp4" && ext != ".mkv" && ext != ".avi" && ext != ".m3u8") { ext = ".mp4" }
	return fmt.Sprintf("http://{HOST}/%s/{USER}/{PASS}/%s%s", pasta, vID, ext)
}
func montarM3U() []byte {
	var todas []M3UEntry
	for _, fonte := range Env.Fontes {
		m3uURL := fmt.Sprintf("http://%s/get.php?username=%s&password=%s&type=m3u_plus&output=mpegts", fonte.Host, fonte.User, fonte.Pass)
		req, _ := http.NewRequest("GET", m3uURL, nil); resp, err := httpClient.Do(req); if err != nil || resp.StatusCode != 200 { continue }
		scanner := bufio.NewScanner(resp.Body); scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024*50); var infoLine string; esperandoURL := false
		for scanner.Scan() {
			line := strings.TrimSpace(scanner.Text()); if line == "" || strings.Contains(line, "#EXTM3U") || strings.Contains(line, "#EXT-X-SESSION") { continue }
			if strings.HasPrefix(line, "#EXTINF") { infoLine = line; esperandoURL = true; continue }
			if esperandoURL && strings.HasPrefix(line, "http") {
				if fonte.ServeVod() && !fonte.ServeLive() { if !strings.Contains(line, "/movie/") && !strings.Contains(line, "/series/") { esperandoURL = false; continue } }
				if fonte.ServeLive() && !fonte.ServeVod() { if strings.Contains(line, "/movie/") || strings.Contains(line, "/series/") { esperandoURL = false; continue } }
				group := extrairGroupTitle(infoLine); if isOcultaParaTodos(group, "live") && !strings.Contains(line, "/movie/") && !strings.Contains(line, "/series/") { esperandoURL = false; continue }
				tipoC := "movie"; if !strings.Contains(line, "/movie/") && !strings.Contains(line, "/series/") { tipoC = "live" }; if strings.Contains(line, "/series/") { tipoC = "series" }
				if isOcultaParaTodos(group, tipoC) { esperandoURL = false; continue }
				novoNome, ordem := getCatInfo(group, tipoC); fi := limparURLsFonte(infoLine, fonte); if novoNome != group && group != "" { fi = renomearGroupTitle(fi, group, novoNome) }
				todas = append(todas, M3UEntry{InfoLine: fi, URLLine: formatarURLM3U(limparURLsFonte(line, fonte), fonte.ID), Group: novoNome, Ordem: ordem}); esperandoURL = false
			}
		}
		resp.Body.Close()
	}
	sort.SliceStable(todas, func(i, j int) bool { return todas[i].Ordem < todas[j].Ordem }); var sb strings.Builder; sb.WriteString("#EXTM3U\n")
	for _, e := range todas { sb.WriteString(e.InfoLine + "\n" + e.URLLine + "\n") }; return []byte(sb.String())
}

func xtreamAPIHandler(w http.ResponseWriter, r *http.Request) {
	setCORS(w); if r.Method == "OPTIONS" { w.WriteHeader(204); return }
	u := r.URL.Query().Get("username"); p := r.URL.Query().Get("password"); action := r.URL.Query().Get("action")
	expDate, maxCons, bouquet, valido := validarUsuarioCache(u, p)
	if !valido { if action == "" { w.Header().Set("Content-Type", "application/json"); w.Write([]byte(`{"user_info":{"auth":0}}`)) } else { http.Error(w, "NEGADO", 401) }; return }
	ip := pegarIP(r); if ipBloqueado(ip) { http.Error(w, "ACESSO NEGADO", 403); return }
	ativas := 0
	if !isWebPlayer(ip) {
		permitido, a, _ := verificarIP(u, ip, maxCons); ativas = a; go registrarIPCliente(ip, u, r.Header.Get("User-Agent"))
		if !permitido { if action == "" { w.Header().Set("Content-Type", "application/json"); w.Write([]byte(fmt.Sprintf(`{"user_info":{"auth":1,"status":"Active","username":"%s","max_connections":"%d","active_cons":"%d","message":"Limite de telas atingido."}}`, u, maxCons, ativas))) } else { http.Error(w, "LIMITE DE TELAS", 403) }; return }
	}
	if action == "" {
		agora := time.Now(); expStr := fmt.Sprintf(`"%d"`, expDate); if expDate == 0 { expStr = `"null"` }
		var buf bytes.Buffer; buf.Grow(512)
		fmt.Fprintf(&buf, `{"user_info":{"username":"%s","password":"%s","message":"Welcome to XUI.one","auth":1,"status":"Active","exp_date":%s,"is_trial":"0","active_cons":"%d","created_at":"%d","max_connections":"%d","allowed_output_formats":["m3u8","ts","rtmp"]},"server_info":{"xui":true,"version":"1.5.13","revision":null,"url":"%s","port":"80","https_port":"443","server_protocol":"http","rtmp_port":"8880","timezone":"America/Sao_Paulo","timestamp_now":%d,"time_now":"%s"}}`, u, p, expStr, ativas, agora.Unix()-86400, maxCons, r.Host, agora.Unix(), agora.Format("2006-01-02 15:04:05"))
		escreverResposta(w, r, "application/json", buf.Bytes()); return
	}
	isHeavy := action == "get_live_categories" || action == "get_vod_categories" || action == "get_series_categories" || action == "get_live_streams" || action == "get_vod_streams" || action == "get_series"
	if isHeavy {
		CacheLock.RLock(); dados := ApiCache[action]; CacheLock.RUnlock()
		if len(dados) == 0 { atualizarTudo(); CacheLock.RLock(); dados = ApiCache[action]; CacheLock.RUnlock() }
		if bouquet == "COMPLETO S/ ADULTOS" && (action == "get_live_categories" || action == "get_vod_categories" || action == "get_series_categories") { dados = filtrarCatsAdulto(dados, action) }
		if bouquet == "COMPLETO S/ ADULTOS" && (action == "get_live_streams" || action == "get_vod_streams" || action == "get_series") { dados = filtrarStreamsAdulto(dados, action) }
		resultado := substituir(dados, u, p, r.Host); ua := r.Header.Get("User-Agent"); extensao := ""
		if isAppAntigo(ua) { extensao = Env.FormatoCanal }; resultado = bytes.ReplaceAll(resultado, []byte("{EXT_LIVE}"), []byte(extensao))
		escreverResposta(w, r, "application/json", resultado); return
	}
	if len(Env.Fontes) == 0 { http.Error(w, "Sem fontes", 502); return }
	fonteParaReq := Env.Fontes[0]
	for _, pk := range []string{"stream_id", "series_id", "vod_id"} {
		pv := r.URL.Query().Get(pk); if pv != "" { if fID, oID, ok := parseVirtualID(pv); ok { if f, found := getFontePorID(fID); found { fonteParaReq = f; q := r.URL.Query(); q.Set(pk, oID); r.URL.RawQuery = q.Encode() } }; break }
	}
	if action == "get_short_epg" || action == "get_simple_data_table" {
		for _, f := range Env.Fontes { if f.ServeLive() { fonteParaReq = f; break } }
		if sid := r.URL.Query().Get("stream_id"); sid != "" { if fID, oID, ok := parseVirtualID(sid); ok { if f, found := getFontePorID(fID); found { fonteParaReq = f; q := r.URL.Query(); q.Set("stream_id", oID); r.URL.RawQuery = q.Encode() } } }
	}
	urlF := fmt.Sprintf("http://%s/player_api.php?username=%s&password=%s&action=%s", fonteParaReq.Host, fonteParaReq.User, fonteParaReq.Pass, action)
	for k, v := range r.URL.Query() { if k != "username" && k != "password" && k != "action" { urlF += fmt.Sprintf("&%s=%s", k, v[0]) } }
	rq, _ := http.NewRequest("GET", urlF, nil); rq.Header.Set("User-Agent", r.Header.Get("User-Agent"))
	rsp, err := httpClient.Do(rq); if err != nil { http.Error(w, "Erro", 502); return }; defer rsp.Body.Close(); body, _ := io.ReadAll(rsp.Body)
	resultado := []byte(limparURLsFonte(string(body), fonteParaReq)); if action == "get_series_info" { resultado = virtualizarEpisodios(resultado, fonteParaReq.ID) }
	escreverResposta(w, r, "application/json", substituir(resultado, u, p, r.Host))
}

func filtrarCatsAdulto(dados []byte, action string) []byte {
	tipoConteudo := "live"; if strings.Contains(action, "vod") { tipoConteudo = "movie" }; if strings.Contains(action, "series") { tipoConteudo = "series" }
	var cats []map[string]interface{}; if json.Unmarshal(dados, &cats) != nil { return dados }; var filtradas []map[string]interface{}
	for _, cat := range cats { nome, _ := cat["category_name"].(string); if !isFiltradaSemAdultos(nome, tipoConteudo) { filtradas = append(filtradas, cat) } }
	if filtradas == nil { return []byte("[]") }; return marshalJSON(filtradas)
}
func filtrarStreamsAdulto(dados []byte, action string) []byte {
	tipoConteudo := "live"; if strings.Contains(action, "vod") { tipoConteudo = "movie" }; if strings.Contains(action, "series") { tipoConteudo = "series" }
	adultoCatIDs := make(map[string]bool)
	rows, err := dbMerger.Query("SELECT virtual_id FROM categorias WHERE tipo=?", tipoConteudo)
	if err == nil {
		for rows.Next() { var vid string; rows.Scan(&vid); var nomeFinal string; dbMerger.QueryRow("SELECT nome_final FROM categorias WHERE virtual_id=? AND tipo=?", vid, tipoConteudo).Scan(&nomeFinal); if isFiltradaSemAdultos(nomeFinal, tipoConteudo) { adultoCatIDs[vid] = true } }; rows.Close()
	}
	if len(adultoCatIDs) == 0 { return dados }
	var items []json.RawMessage; if json.Unmarshal(dados, &items) != nil { return dados }; var buf bytes.Buffer; buf.WriteByte('['); first := true
	for _, rawItem := range items { var peek struct { CatID interface{} `json:"category_id"` }; json.Unmarshal(rawItem, &peek); catID := fmt.Sprintf("%v", peek.CatID); if adultoCatIDs[catID] { continue }; if !first { buf.WriteByte(',') }; buf.Write(rawItem); first = false }
	buf.WriteByte(']'); return buf.Bytes()
}

func gerarListaM3U(w http.ResponseWriter, r *http.Request) {
	setCORS(w); if r.Method == "OPTIONS" { w.WriteHeader(204); return }
	u := r.URL.Query().Get("username"); p := r.URL.Query().Get("password"); _, maxCons, bouquet, valido := validarUsuarioCache(u, p)
	if !valido { http.Error(w, "ACESSO NEGADO", 401); return }
	ip := pegarIP(r); if ipBloqueado(ip) { http.Error(w, "ACESSO NEGADO", 403); return }
	if !isWebPlayer(ip) {
		permitido, _, _ := verificarIP(u, ip, maxCons); go registrarIPCliente(ip, u, r.Header.Get("User-Agent"))
		if !permitido { http.Error(w, "LIMITE DE TELAS ATINGIDO", 403); return }
	}
	CacheLock.RLock(); lista := M3UCache; CacheLock.RUnlock(); listaStr := string(lista)
	if bouquet == "COMPLETO S/ ADULTOS" { listaStr = filtrarM3UAdulto(listaStr) }
	outputParam := strings.ToLower(r.URL.Query().Get("output")); ua := r.Header.Get("User-Agent"); extensao := ""
	if outputParam == "hls" { extensao = ".m3u8" } else if isAppAntigo(ua) { extensao = Env.FormatoCanal }
	replacer := strings.NewReplacer("{USER}", u, "{PASS}", p, "{HOST}", r.Host, "{EXT_LIVE}", extensao)
	w.Header().Set("Content-Type", "application/x-mpegurl"); w.Header().Set("Connection", "keep-alive")
	nomeArquivo := "lista_king.m3u"; if outputParam == "hls" { nomeArquivo = "lista_king_hls.m3u" }
	w.Header().Set("Content-Disposition", fmt.Sprintf(`attachment; filename="%s"`, nomeArquivo))
	aceitaGzip := strings.Contains(r.Header.Get("Accept-Encoding"), "gzip"); if aceitaGzip { w.Header().Set("Content-Encoding", "gzip") }
	if flusher, ok := w.(http.Flusher); ok { flusher.Flush() }
	if aceitaGzip {
		gz := gzipWriterPool.Get().(*gzip.Writer); gz.Reset(w); replacer.WriteString(gz, listaStr); gz.Close(); gzipWriterPool.Put(gz)
	} else { replacer.WriteString(w, listaStr) }
}
func filtrarM3UAdulto(m3u string) string {
	lines := strings.Split(m3u, "\n"); var sb strings.Builder; sb.Grow(len(m3u)); pular := false
	for _, line := range lines {
		if strings.HasPrefix(line, "#EXTINF") {
			group := extrairGroupTitle(line); tipoC := "live"; pular = false
			if isFiltradaSemAdultos(group, tipoC) || isFiltradaSemAdultos(group, "movie") || isFiltradaSemAdultos(group, "series") { pular = true; continue }
			sb.WriteString(line + "\n"); continue
		}
		if pular { pular = false; continue }; sb.WriteString(line + "\n")
	}
	return sb.String()
}

// ============================================================
// 📡 RESTREAMER 24H (O MULTIPLEXADOR DEFINITIVO)
// ============================================================
type StreamHub struct {
	StreamID  string
	Nome      string
	Categoria string
	URL       string
	Clients   map[chan []byte]bool
	mu        sync.RWMutex
	Stop      chan bool
	StartTime time.Time
	History   []byte       // ⚡ O reservatório gigante
	HistoryMu sync.RWMutex // ⚡ Trava do reservatório
}

var activeHubs = make(map[string]*StreamHub)
var hubsMu sync.Mutex

func iniciarRestreamers() {
	for {
		time.Sleep(10 * time.Second)
		rows, err := dbMerger.Query("SELECT fonte_id, stream_id_original, tipo FROM canal_24h")
		if err != nil { continue }
		
		ativas := make(map[string]bool)
		for rows.Next() {
			var fID int; var sID, t string
			rows.Scan(&fID, &sID, &t)
			key := fmt.Sprintf("%d_%s_%s", fID, sID, t)
			ativas[key] = true

			hubsMu.Lock()
			if _, exists := activeHubs[key]; !exists {
				var jdata string
				nomeCanal := "Canal 24h"
				nomeCategoria := "Sem Categoria"

				sqlInfo := `SELECT s.json_data, COALESCE(c.nome_final, 'Sem Categoria') 
				            FROM streams s 
				            LEFT JOIN categorias c ON c.virtual_id=s.virtual_cat_id AND c.tipo=s.tipo 
				            WHERE s.fonte_id=? AND s.stream_id_original=? AND s.tipo=?`
				
				if dbMerger.QueryRow(sqlInfo, fID, sID, t).Scan(&jdata, &nomeCategoria) == nil {
					var peek map[string]interface{}
					if json.Unmarshal([]byte(jdata), &peek) == nil {
						if n, ok := peek["name"].(string); ok { nomeCanal = n }
					}
				}

				hub := &StreamHub{
					StreamID:  sID,
					Nome:      nomeCanal,
					Categoria: nomeCategoria,
					URL:       gerarURLFonte(fID, sID, t),
					Clients:   make(map[chan []byte]bool),
					Stop:      make(chan bool),
					StartTime: time.Now(),
				}
				activeHubs[key] = hub
				go rodarHub(hub)
			}
			hubsMu.Unlock()
		}
		rows.Close()

		hubsMu.Lock()
		for key, hub := range activeHubs {
			if !ativas[key] {
				close(hub.Stop)
				delete(activeHubs, key)
			}
		}
		hubsMu.Unlock()
	}
}

func gerarURLFonte(fID int, sID string, tipo string) string {
	var urlCustom string
	dbMerger.QueryRow("SELECT novo_url FROM url_overrides WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fID, sID, tipo).Scan(&urlCustom)
	if urlCustom != "" { return urlCustom }
	
	f, ok := getFontePorID(fID)
	if !ok { return "" }
	pasta := tipo
	if pasta == "live" { return fmt.Sprintf("http://%s/live/%s/%s/%s.ts", f.Host, f.User, f.Pass, sID) }
	return fmt.Sprintf("http://%s/%s/%s/%s/%s.mp4", f.Host, pasta, f.User, f.Pass, sID)
}

// ⚡ O DETETIVE DE APARELHOS: Descobre se o cliente aguenta a porrada!
// ⚡ O DETETIVE DE APARELHOS (Versão Suprema de 3 Níveis)
func getCacheSizeForClient(ua string) int {
	ua = strings.ToLower(ua)
	
	// 1. TVs PARRUDAS (Abrem instantâneo e precisam de gordura) -> 2MB
	if strings.Contains(ua, "tivimate") || strings.Contains(ua, "tizen") || 
	   strings.Contains(ua, "webos") || strings.Contains(ua, "smarttv") || 
	   strings.Contains(ua, "smart-tv") || strings.Contains(ua, "tv") || 
	   strings.Contains(ua, "box") || strings.Contains(ua, "stb") {
		return 2 * 1024 * 1024 // 2 MB
	}

	// 2. CELULARES E PCS (App crasha com muita coisa) -> 128KB
	if strings.Contains(ua, "windows") || strings.Contains(ua, "macintosh") || 
	   strings.Contains(ua, "mobile") || strings.Contains(ua, "iphone") || 
	   strings.Contains(ua, "ipad") || strings.Contains(ua, "vlc") || 
	   strings.Contains(ua, "pc") {
		return 512 * 1024 // 128 KB
	}

	// 3. APLICATIVOS GENÉRICOS / MENTIROSOS (Smarters, XCIPTV, etc)
	// O Ponto Doce de segurança: não crasha o PC e não trava a TV!
	return 512 * 1024 // 512 KB
}

// getDelayConfig: quanto cache no fast start por tipo de dispositivo.
// TV/Box: 2MB inicial — player lento, precisa de mais gordura.
// PC/Celular: 512KB inicial — player rápido, menos é mais estável.
func getDelayConfig(ua string) int {
	ua = strings.ToLower(ua)
	if strings.Contains(ua, "tivimate") || strings.Contains(ua, "tizen") ||
		strings.Contains(ua, "webos") || strings.Contains(ua, "smarttv") ||
		strings.Contains(ua, "smart-tv") || strings.Contains(ua, "tv") ||
		strings.Contains(ua, "box") || strings.Contains(ua, "stb") {
		return 2 * 1024 * 1024
	}
	return 512 * 1024
}

func rodarHub(h *StreamHub) {
	const MaxHistorySize = 2 * 1024 * 1024

	// Quando o hub parar, fecha todos os canais dos clientes.
	// Sem isso ficam travados em "for chunk := range c" para sempre.
	defer func() {
		h.mu.Lock()
		for c := range h.Clients { close(c) }
		h.Clients = make(map[chan []byte]bool)
		h.mu.Unlock()
	}()

	for {
		select { case <-h.Stop: return; default: }
		
		req, _ := http.NewRequest("GET", h.URL, nil)
		req.Header.Set("User-Agent", "IPTV Smarters Pro")
		
		resp, err := streamClient.Do(req)
		if err != nil {
			time.Sleep(2 * time.Second)
			continue
		}
		if resp.StatusCode != 200 {
			resp.Body.Close()
			time.Sleep(2 * time.Second)
			continue
		}

		buf := make([]byte, 64*1024)
		for {
			select { case <-h.Stop: resp.Body.Close(); return; default: }
			
			n, err := resp.Body.Read(buf)
			if n > 0 {
				chunk := make([]byte, n)
				copy(chunk, buf[:n])
				
				h.HistoryMu.Lock()
				h.History = append(h.History, chunk...)
				if len(h.History) > MaxHistorySize {
					h.History = h.History[len(h.History)-MaxHistorySize:]
				}
				h.HistoryMu.Unlock()
				
				h.mu.RLock()
				for c := range h.Clients {
					select { case c <- chunk: default: }
				}
				h.mu.RUnlock()
			}
			if err != nil { break } 
		}
		resp.Body.Close()
	}
}


// ============================================================
// ▶️ PLAY HANDLER (Lógica Suprema e Estável)
// ============================================================
func playHandler(w http.ResponseWriter, r *http.Request) {
	setCORS(w)
	if r.Method == "OPTIONS" { w.WriteHeader(204); return }
	caminho := strings.TrimPrefix(r.URL.Path, "/")
	if caminho == "" || caminho == "favicon.ico" { w.WriteHeader(http.StatusOK); return }
	if strings.HasPrefix(caminho, "painel") || strings.HasPrefix(caminho, "merger") { return }

	partes := strings.Split(caminho, "/")
	tipo := ""
	if len(partes) >= 4 && (partes[0] == "live" || partes[0] == "movie" || partes[0] == "series") { tipo, partes = partes[0], partes[1:] }
	if len(partes) < 3 { http.Error(w, "Formato invalido", 400); return }

	user, pass := partes[0], partes[1]
	_, maxCons, _, valido := validarUsuarioCache(user, pass)
	if !valido { http.Error(w, "NEGADO", 401); return }
	ip := pegarIP(r); if ipBloqueado(ip) { http.Error(w, "ACESSO NEGADO", 403); return }
	
	if !isWebPlayer(ip) {
		permitido, _, _ := verificarIP(user, ip, maxCons)
		go registrarIPCliente(ip, user, r.Header.Get("User-Agent"))
		if !permitido { http.Error(w, "LIMITE DE TELAS ATINGIDO", 403); return }
	}

	ult := partes[len(partes)-1]; idStr, extP := ult, ""
	if idx := strings.LastIndex(ult, "."); idx != -1 { idStr, extP = ult[:idx], ult[idx:] }

	fID, idOrig, isV := parseVirtualID(idStr)
	var fa FonteConfig
	if isV {
		f, found := getFontePorID(fID); if !found { http.Error(w, "Fonte não encontrada", 404); return }
		fa = f
	} else {
		if len(Env.Fontes) > 0 { fa = Env.Fontes[0] } else { http.Error(w, "Sem fontes", 502); return }
		idOrig = idStr
	}

	pasta := tipo
	if pasta == "" { if extP == ".mp4" || extP == ".mkv" || extP == ".avi" { pasta = "movie" } else { pasta = "live" } }

	arq := idOrig + extP
	if len(partes) > 3 {
		sp := partes[2:]
		for i, s := range sp {
			sn, se := s, ""; if idx := strings.LastIndex(s, "."); idx != -1 { sn, se = s[:idx], s[idx:] }
			if _, o, w := parseVirtualID(sn); w { sp[i] = o + se }
		}
		ui := len(sp) - 1; if !strings.Contains(sp[ui], ".") { sp[ui] += ".mp4" }
		arq = strings.Join(sp, "/")
	}

	if pasta == "live" && extP == "" { arq = idOrig }
	urlF := fmt.Sprintf("http://%s/%s/%s/%s/%s", fa.Host, pasta, fa.User, fa.Pass, arq)

	var urlCustom string
	if dbMerger.QueryRow("SELECT novo_url FROM url_overrides WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fa.ID, idOrig, pasta).Scan(&urlCustom) == nil && urlCustom != "" { urlF = urlCustom }

	// ⚡ 1. VERIFICA SE O CANAL ESTÁ NO MODO "DIRETO"
	var forceDirect int
	dbMerger.QueryRow("SELECT 1 FROM stream_direto WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fa.ID, idOrig, pasta).Scan(&forceDirect)
	if forceDirect == 1 {
		http.Redirect(w, r, urlF, http.StatusFound)
		return
	}

	// ⚡ 2. VERIFICA SE É CANAL 24H
	var is24h bool
	if pasta == "live" {
		var c int
		dbMerger.QueryRow("SELECT 1 FROM canal_24h WHERE fonte_id=? AND stream_id_original=? AND tipo=?", fa.ID, idOrig, pasta).Scan(&c)
		is24h = (c == 1)
	}

	var hub *StreamHub
	if is24h {
		key := fmt.Sprintf("%d_%s_%s", fa.ID, idOrig, pasta)
		hubsMu.Lock()
		hub = activeHubs[key]
		hubsMu.Unlock()
	}

        // ⚡ 3. ENTREGA O CANAL 24H
	if is24h && hub != nil {
		w.Header().Set("Content-Type", "video/mp2t")
		w.Header().Set("Connection", "keep-alive")
		w.Header().Set("Cache-Control", "no-cache, no-store")
		w.Header().Set("X-Accel-Buffering", "no")
		w.WriteHeader(200)

		flusher, canFlush := w.(http.Flusher)
		initialBytes := getDelayConfig(r.Header.Get("User-Agent"))

		// PASSO 1: Copia fast start para buffer local SEM registrar o cliente ainda.
		// Enquanto enviamos o cache, o cliente 1 não é afetado de forma alguma.
		var fastStart []byte
		hub.HistoryMu.RLock()
		if hl := len(hub.History); hl > 0 {
			sz := initialBytes; if sz > hl { sz = hl }
			fastStart = make([]byte, sz)
			copy(fastStart, hub.History[hl-sz:])
		}
		hub.HistoryMu.RUnlock()

		// PASSO 2: Envia o cache. Cliente ainda NÃO está no hub.
		if len(fastStart) > 0 { w.Write(fastStart); if canFlush { flusher.Flush() } }

		// PASSO 3: Entra no hub — direto no ao vivo, sem fila acumulada.
		// Buffer pequeno (32): já tem o cache, não precisa de fila grande.
		c := make(chan []byte, 32)
		hub.mu.Lock(); hub.Clients[c] = true; hub.mu.Unlock()
		defer func() { hub.mu.Lock(); delete(hub.Clients, c); hub.mu.Unlock() }()

		ctx := r.Context()
		for {
			select {
			case <-ctx.Done():
				return
			case chunk, ok := <-c:
				if !ok { return }
				if _, err := w.Write(chunk); err != nil { return }
				if canFlush { flusher.Flush() }
			}
		}
	}

	// ⚡ 4. O NOVO PROXY "TIRO ÚNICO" (Se não for canal 24h)
	cc := &http.Client{
		Transport: &http.Transport{
			TLSClientConfig:       &tls.Config{InsecureSkipVerify: true},
			ResponseHeaderTimeout: 15 * time.Second,
			DisableCompression:    true,            
			ForceAttemptHTTP2:     false,           
		},
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			return http.ErrUseLastResponse
		},
	}

	reqOut, _ := http.NewRequest("GET", urlF, nil)
	
	for k, vv := range r.Header {
		h := strings.ToLower(k)
		if h == "host" || h == "accept-encoding" || h == "connection" { continue }
		for _, v := range vv { reqOut.Header.Add(k, v) }
	}

	rsp, err := cc.Do(reqOut)
	if err != nil { http.Error(w, "Erro ao contatar fonte", 502); return }

	if rsp.StatusCode >= 300 && rsp.StatusCode <= 303 {
		loc := rsp.Header.Get("Location")
		rsp.Body.Close()
		
		if loc != "" && !linkExpoeCredenciais(loc) {
			http.Redirect(w, r, loc, http.StatusFound)
			return
		}
		if loc != "" { proxyStream(w, r, loc) } else { proxyStream(w, r, urlF) }
		return
	}

	defer rsp.Body.Close()

	for k, vv := range rsp.Header {
		h := strings.ToLower(k)
		if h == "transfer-encoding" || h == "content-length" { continue }
		for _, v := range vv { w.Header().Add(k, v) }
	}

	if strings.HasSuffix(urlF, ".ts") {
		w.Header().Set("Content-Type", "video/mp2t")
	}
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Accel-Buffering", "no")
	w.WriteHeader(rsp.StatusCode)

	bufPtr := bufPool.Get().(*[]byte)
	defer bufPool.Put(bufPtr)
	
	io.CopyBuffer(w, rsp.Body, *bufPtr)
}

func proxyStream(w http.ResponseWriter, r *http.Request, targetURL string) {
	setCORS(w)
	reqP, _ := http.NewRequest(r.Method, targetURL, nil)
	
	for k, vv := range r.Header {
		h := strings.ToLower(k)
		if h == "host" || h == "accept-encoding" || h == "connection" { continue }
		for _, v := range vv { reqP.Header.Add(k, v) }
	}
	
	resp, err := streamClient.Do(reqP)
	if err != nil { http.Error(w, "Offline", 502); return }
	defer resp.Body.Close()

	for k, vv := range resp.Header {
		h := strings.ToLower(k)
		if h == "transfer-encoding" || h == "content-length" { continue }
		for _, v := range vv { w.Header().Add(k, v) }
	}
	
	w.Header().Set("Connection", "keep-alive")
	w.Header().Set("X-Accel-Buffering", "no")
	w.WriteHeader(resp.StatusCode)

	io.Copy(w, resp.Body)
}

// ============================================================
// 🤖 SIGMA HANDLER E OUTROS
// ============================================================
func detectarPainel(r *http.Request) string {
	path := r.URL.Path
	for _, painel := range Env.SigmaPaineis { if strings.Contains(path, painel) { return painel } }
	return ""
}

func sigmaHandler(w http.ResponseWriter, r *http.Request) {
	r.ParseForm()
	acao := r.FormValue("action")
	painel := detectarPainel(r)
	w.Header().Set("Content-Type", "application/json")

	switch acao {
	case "get_groups": w.Write([]byte(`[{"group_id":"1","group_name":"Administrators"},{"group_id":"2","group_name":"Resellers"}]`))
	case "get_packages": w.Write([]byte(`[{"id":"4","package_name":"COMPLETO C/ ADULTOS","is_addon":"0","is_trial":"1","is_official":"1","trial_credits":"0","official_credits":"0","trial_duration":"4","trial_duration_in":"hours","official_duration":"1","official_duration_in":"months","groups":"[2]","bouquets":"[5]","addon_packages":null,"is_line":"1","is_mag":"0","is_e2":"0","is_restreamer":"0","is_isplock":"0","output_formats":"[1,2,3]","max_connections":"5","force_server_id":"0","forced_country":null,"lock_device":"0","check_compatible":"1"},{"id":"5","package_name":"COMPLETO S/ ADULTOS","is_addon":"0","is_trial":"1","is_official":"1","trial_credits":"0","official_credits":"0","trial_duration":"4","trial_duration_in":"hours","official_duration":"1","official_duration_in":"months","groups":"[2]","bouquets":"[6]","addon_packages":null,"is_line":"1","is_mag":"0","is_e2":"0","is_restreamer":"0","is_isplock":"0","output_formats":"[1,2,3]","max_connections":"5","force_server_id":"0","forced_country":null,"lock_device":"0","check_compatible":"1"}]`))
	case "create_line":
		user, pass := r.FormValue("username"), r.FormValue("password")
		maxCons, _ := strconv.Atoi(r.FormValue("max_connections"))
		if maxCons == 0 { maxCons = 1 }
		var expUnix int64 = 0
		if rawExp := r.FormValue("exp_date"); rawExp != "" { expUnix = parseExpDate(rawExp) }
		enabled := 1; if r.FormValue("enabled") == "0" { enabled = 0 }
		bouquet := "COMPLETO C/ ADULTOS"; if strings.Contains(r.FormValue("bouquets_selected"), "6") { bouquet = "COMPLETO S/ ADULTOS" }
		isTrial := 0; if r.FormValue("is_trial") == "1" { isTrial = 1 }
		var rowID int64
		res, err := dbUsers.Exec("INSERT INTO clientes (username, password, exp_date, max_connections, bouquet, created_at, painel, enabled, is_trial) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)", user, pass, expUnix, maxCons, bouquet, time.Now().Unix(), painel, enabled, isTrial)
		if err != nil {
			dbUsers.Exec("UPDATE clientes SET password=?, exp_date=?, max_connections=?, bouquet=?, enabled=?, is_trial=? WHERE username=? AND painel=?", pass, expUnix, maxCons, bouquet, enabled, isTrial, user, painel)
			dbUsers.QueryRow("SELECT id FROM clientes WHERE username=? AND painel=?", user, painel).Scan(&rowID)
		} else { rowID, _ = res.LastInsertId() }
		invalidarAuthCache()
		status := "1"; if enabled == 0 || (expUnix > 0 && expUnix < time.Now().Unix()) { status = "0" }
		w.Write([]byte(fmt.Sprintf(`{"status":"STATUS_SUCCESS","data":{"id":"%d","username":"%s","password":"%s","exp_date":"%d","max_connections":"%d","status":"%s","enabled":"%d"}}`, rowID, user, pass, expUnix, maxCons, status, enabled)))
	case "delete_line":
		dbUsers.Exec("DELETE FROM clientes WHERE id=? AND painel=?", r.FormValue("id"), painel)
		invalidarAuthCache(); w.Write([]byte(`{"status":"STATUS_SUCCESS","message":"Linha deletada."}`))
	case "get_lines":
		search := r.FormValue("search[value]"); var rows *sql.Rows; var err error
		if search != "" { rows, err = dbUsers.Query("SELECT id, username, password, exp_date, max_connections, created_at, bouquet, COALESCE(enabled, 1), COALESCE(admin_notes, ''), COALESCE(is_trial, 0) FROM clientes WHERE painel = ? AND username LIKE ?", painel, "%"+search+"%")
		} else { rows, err = dbUsers.Query("SELECT id, username, password, exp_date, max_connections, created_at, bouquet, COALESCE(enabled, 1), COALESCE(admin_notes, ''), COALESCE(is_trial, 0) FROM clientes WHERE painel = ?", painel) }
		if err != nil { w.Write([]byte(`{"status":"STATUS_SUCCESS","data":[],"recordsTotal":"0","recordsFiltered":"0"}`)); return }
		defer rows.Close(); var buf bytes.Buffer; buf.WriteString(`{"status":"STATUS_SUCCESS","data":[`); first, total := true, 0
		for rows.Next() {
			var id, maxCons, enabled, isTrial int; var user, pass, bouquet, adminNotes string; var expDate, created int64
			rows.Scan(&id, &user, &pass, &expDate, &maxCons, &created, &bouquet, &enabled, &adminNotes, &isTrial)
			status := "1"; if enabled == 0 || (expDate > 0 && expDate < time.Now().Unix()) { status = "0" }
			packageID := "4"; if bouquet == "COMPLETO S/ ADULTOS" { packageID = "5" }
			if !first { buf.WriteByte(',') }
			fmt.Fprintf(&buf, `{"id":"%d","username":"%s","password":"%s","exp_date":"%d","max_connections":"%d","status":"%s","enabled":"%d","package_id":"%s","created_at":"%d","is_trial":"%d","active_cons":"0","admin_notes":"%s"}`, id, user, pass, expDate, maxCons, status, enabled, packageID, created, isTrial, adminNotes)
			first = false; total++
		}
		fmt.Fprintf(&buf, `],"recordsTotal":"%d","recordsFiltered":"%d"}`, total, total); w.Write(buf.Bytes())
	case "get_users": w.Write([]byte(fmt.Sprintf(`{"status":"STATUS_SUCCESS","data":[{"id":"1","username":"%s","password":"","email":"","member_group_id":"0","owner_id":"1","status":"1","credits":"100000","notes":"","date_registered":"%d","last_login":"%d"}],"recordsTotal":"1","recordsFiltered":"1"}`, painel, time.Now().Unix()-86400*30, time.Now().Unix())))
	case "create_user": w.Write([]byte(fmt.Sprintf(`{"status":"STATUS_SUCCESS","data":{"id":"1","username":"%s","status":"1","credits":"100000"}}`, r.FormValue("username"))))
	case "edit_user": w.Write([]byte(fmt.Sprintf(`{"status":"STATUS_SUCCESS","data":{"id":"%s","username":"%s","status":"1","credits":"100000"}}`, r.FormValue("id"), r.FormValue("username"))))
	case "mysql_query":
		limit, offset := 10000, 0
		rows, err := dbUsers.Query("SELECT id, username FROM clientes WHERE painel = ? LIMIT ? OFFSET ?", painel, limit, offset)
		if err != nil { w.Write([]byte(`{"status":"STATUS_SUCCESS","data":[]}`)); return }
		defer rows.Close(); var buf bytes.Buffer; buf.WriteString(`{"status":"STATUS_SUCCESS","data":[`); first := true
		for rows.Next() { var id int; var user string; rows.Scan(&id, &user); if !first { buf.WriteByte(',') }; fmt.Fprintf(&buf, `{"id":"%d","username":"%s"}`, id, user); first = false }
		buf.WriteString(`]}`); w.Write(buf.Bytes())
	case "live_connections":
		total, lista := getConexoesAtivas(); var buf bytes.Buffer; buf.WriteString(`{"status":"STATUS_SUCCESS","data":[`)
		if r.FormValue("start") == "0" {
			for i, c := range lista { if i > 0 { buf.WriteByte(',') }; fmt.Fprintf(&buf, `{"username":"%s","ip":"%s","expira":"%s"}`, c["username"], c["ip"], c["expira"]) }
		}
		fmt.Fprintf(&buf, `],"total":%d}`, total); w.Write(buf.Bytes())
	default: w.Write([]byte(`{"status":"STATUS_SUCCESS","message":"OK"}`))
	}
}

func mostrarBancoNoTerminal() {
	rows, err := dbUsers.Query("SELECT id, username, password, exp_date, max_connections, bouquet, painel, COALESCE(enabled, 1) FROM clientes")
	if err != nil { return }
	defer rows.Close()
	fmt.Println("\n====================================================================================================")
	fmt.Printf("%-5s | %-15s | %-12s | %-20s | %-5s | %-20s | %-12s | %-4s\n", "ID", "USUÁRIO", "SENHA", "VALIDADE", "TELAS", "PLANO", "PAINEL", "ON")
	fmt.Println("----------------------------------------------------------------------------------------------------")
	for rows.Next() {
		var id, maxCons, enabled int; var user, pass, bouquet, painel string; var expDate int64
		rows.Scan(&id, &user, &pass, &expDate, &maxCons, &bouquet, &painel, &enabled)
		dataExpStr := "Vitalício"; if expDate > 0 { dataExpStr = time.Unix(expDate, 0).Format("02/01/2006 15:04:05") }
		if painel == "" { painel = "---" }
		statusStr := "✅"; if enabled == 0 { statusStr = "🚫" } else if expDate > 0 && expDate < time.Now().Unix() { statusStr = "⏰" }
		fmt.Printf("%-5d | %-15s | %-12s | %-20s | %-5d | %-20s | %-12s | %-4s\n", id, user, pass, dataExpStr, maxCons, bouquet, painel, statusStr)
	}
	fmt.Println("====================================================================================================\n")
}

func mostrarEstatisticasPaineis() {
	fmt.Println("\n📊 ESTATÍSTICAS POR PAINEL SIGMA:")
	fmt.Println("============================================================")
	for _, painel := range Env.SigmaPaineis {
		var totalAtivos, totalTeste, totalExpirados, totalBloqueados int
		rows, err := dbUsers.Query("SELECT exp_date, COALESCE(enabled, 1), COALESCE(is_trial, 0) FROM clientes WHERE painel = ?", painel)
		if err != nil { continue }
		agora := time.Now().Unix()
		for rows.Next() {
			var expDate int64; var enabled, isTrial int; rows.Scan(&expDate, &enabled, &isTrial)
			if enabled == 0 { totalBloqueados++ } else if expDate > 0 && expDate < agora { totalExpirados++ } else if isTrial == 1 { totalTeste++ } else { totalAtivos++ }
		}
		rows.Close()
		total := totalAtivos + totalTeste + totalExpirados + totalBloqueados
		fmt.Printf("   📱 %-15s | %d ativos, %d teste, %d expirados, %d bloqueados | Total: %d\n", painel, totalAtivos, totalTeste, totalExpirados, totalBloqueados, total)
	}
	var semPainel int; dbUsers.QueryRow("SELECT COUNT(*) FROM clientes WHERE painel = '' OR painel IS NULL").Scan(&semPainel)
	if semPainel > 0 { fmt.Printf("   ⚠️ %-15s | %d usuários (migração pendente)\n", "SEM PAINEL", semPainel) }
	fmt.Println("============================================================\n")
}

func statsHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json"); agora := time.Now().Unix(); var resultado []map[string]interface{}
	for _, painel := range Env.SigmaPaineis {
		var totalAtivos, totalTeste, totalExpirados, totalBloqueados int
		rows, err := dbUsers.Query("SELECT exp_date, COALESCE(enabled, 1), COALESCE(is_trial, 0) FROM clientes WHERE painel = ?", painel)
		if err != nil { continue }
		for rows.Next() {
			var expDate int64; var enabled, isTrial int; rows.Scan(&expDate, &enabled, &isTrial)
			if enabled == 0 { totalBloqueados++ } else if isTrial == 1 { totalTeste++ } else if expDate > 0 && expDate < agora { totalExpirados++ } else { totalAtivos++ }
		}
		rows.Close()
		resultado = append(resultado, map[string]interface{}{"painel": painel, "ativos": totalAtivos, "teste": totalTeste, "expirados": totalExpirados, "bloqueados": totalBloqueados, "total": totalAtivos + totalTeste + totalExpirados + totalBloqueados})
	}
	json.NewEncoder(w).Encode(resultado)
}

func verificarAdmin(w http.ResponseWriter, r *http.Request) bool {
	user, pass, ok := r.BasicAuth(); if ok && user == Env.AdminUser && pass == Env.AdminPass { return true }
	w.Header().Set("WWW-Authenticate", `Basic realm="GO IPTV Admin"`); http.Error(w, "Acesso negado", 401); return false
}

func apiUsuariosHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	search := r.URL.Query().Get("search"); painelFiltro := r.URL.Query().Get("painel"); statusFiltro := r.URL.Query().Get("status")
	page, _ := strconv.Atoi(r.URL.Query().Get("page")); if page < 1 { page = 1 }; perPage := 100; agora := time.Now().Unix()

	query := "SELECT id, username, password, exp_date, max_connections, bouquet, painel, COALESCE(enabled, 1), COALESCE(admin_notes, ''), COALESCE(created_at, 0), COALESCE(is_trial, 0) FROM clientes WHERE 1=1"
	countQuery := "SELECT COUNT(*) FROM clientes WHERE 1=1"; args := []interface{}{}
	if painelFiltro != "" && painelFiltro != "todos" { query += " AND painel = ?"; countQuery += " AND painel = ?"; args = append(args, painelFiltro) }
	if search != "" { query += " AND username LIKE ?"; countQuery += " AND username LIKE ?"; args = append(args, "%"+search+"%") }

	var total int; dbUsers.QueryRow(countQuery, args...).Scan(&total)
	query += " ORDER BY id DESC LIMIT ? OFFSET ?"; queryArgs := append(args, perPage, (page-1)*perPage)
	rows, err := dbUsers.Query(query, queryArgs...)
	if err != nil { json.NewEncoder(w).Encode(map[string]interface{}{"data": []interface{}{}, "total": 0, "page": page, "pages": 0}); return }
	defer rows.Close()
	
	var lista []map[string]interface{}; host := Env.AdminDNS; if host == "" && len(Env.Fontes) > 0 { host = Env.Fontes[0].Host }
	for rows.Next() {
		var id, maxCons, enabled, isTrial int; var user, pass, bouquet, painel, notes string; var expDate, created int64
		rows.Scan(&id, &user, &pass, &expDate, &maxCons, &bouquet, &painel, &enabled, &notes, &created, &isTrial)
		status := "ativo"; if enabled == 0 { status = "bloqueado" } else if expDate > 0 && expDate < agora { status = "expirado" } else if isTrial == 1 { status = "teste" }
		if statusFiltro != "" && statusFiltro != "todos" && status != statusFiltro { continue }
		validade := "Vitalicio"; if expDate > 0 { validade = time.Unix(expDate, 0).Format("02/01/2006 15:04") }
		criado := ""; if created > 0 { criado = time.Unix(created, 0).Format("02/01/2006 15:04") }
		linkM3U := fmt.Sprintf("http://%s/get.php?username=%s&password=%s&type=m3u_plus&output=mpegts", host, user, pass)
		linkHLS := fmt.Sprintf("http://%s/get.php?username=%s&password=%s&type=m3u_plus&output=hls", host, user, pass)
		lista = append(lista, map[string]interface{}{"id": id, "username": user, "password": pass, "exp_date": expDate, "validade": validade, "max_connections": maxCons, "bouquet": bouquet, "painel": painel, "enabled": enabled, "status": status, "notes": notes, "created_at": criado, "is_trial": isTrial, "link_m3u": linkM3U, "link_hls": linkHLS})
	}
	if lista == nil { lista = []map[string]interface{}{} }; pages := (total + perPage - 1) / perPage
	json.NewEncoder(w).Encode(map[string]interface{}{"data": lista, "total": total, "page": page, "pages": pages, "per_page": perPage})
}

func apiToggleHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	id := r.URL.Query().Get("id"); acao := r.URL.Query().Get("acao"); novoEnabled := 1; if acao == "bloquear" { novoEnabled = 0 }
	dbUsers.Exec("UPDATE clientes SET enabled = ? WHERE id = ?", novoEnabled, id); invalidarAuthCache(); json.NewEncoder(w).Encode(map[string]interface{}{"ok": true})
}

func apiDeleteHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }; w.Header().Set("Content-Type", "application/json"); dbUsers.Exec("DELETE FROM clientes WHERE id = ?", r.URL.Query().Get("id")); invalidarAuthCache(); json.NewEncoder(w).Encode(map[string]interface{}{"ok": true})
}

func apiDeleteExpiredHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }; w.Header().Set("Content-Type", "application/json")
	painelFiltro := r.URL.Query().Get("painel"); agora := time.Now().Unix(); var res sql.Result
	if painelFiltro != "" && painelFiltro != "todos" { res, _ = dbUsers.Exec("DELETE FROM clientes WHERE exp_date > 0 AND exp_date < ? AND painel = ?", agora, painelFiltro) } else { res, _ = dbUsers.Exec("DELETE FROM clientes WHERE exp_date > 0 AND exp_date < ?", agora) }
	n, _ := res.RowsAffected(); invalidarAuthCache(); json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "deletados": n})
}

func apiCriarUsuarioHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }; w.Header().Set("Content-Type", "application/json")
	user := r.URL.Query().Get("username"); pass := r.URL.Query().Get("password"); painel := r.URL.Query().Get("painel"); maxCons, _ := strconv.Atoi(r.URL.Query().Get("max_connections")); dias, _ := strconv.Atoi(r.URL.Query().Get("dias")); isTrial, _ := strconv.Atoi(r.URL.Query().Get("is_trial")); bouquet := r.URL.Query().Get("bouquet")
	if user == "" || pass == "" || painel == "" { json.NewEncoder(w).Encode(map[string]interface{}{"ok": false, "erro": "Preencha todos os campos"}); return }
	if maxCons == 0 { maxCons = 1 }; if bouquet == "" { bouquet = "COMPLETO C/ ADULTOS" }
	var expUnix int64 = 0; if dias > 0 { expUnix = time.Now().Unix() + int64(dias)*86400 } else if isTrial == 1 { expUnix = time.Now().Unix() + 4*3600 }
	_, err := dbUsers.Exec("INSERT INTO clientes (username, password, exp_date, max_connections, bouquet, created_at, painel, enabled, is_trial) VALUES (?, ?, ?, ?, ?, ?, ?, 1, ?)", user, pass, expUnix, maxCons, bouquet, time.Now().Unix(), painel, isTrial)
	if err != nil { json.NewEncoder(w).Encode(map[string]interface{}{"ok": false, "erro": "Usuario ja existe"}); return }
	invalidarAuthCache(); json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "username": user, "password": pass})
}

func apiDeletePainelHandler(w http.ResponseWriter, r *http.Request) {
	if !verificarAdmin(w, r) { return }; w.Header().Set("Content-Type", "application/json")
	painel := r.URL.Query().Get("painel"); if r.URL.Query().Get("senha") != Env.AdminPass { json.NewEncoder(w).Encode(map[string]interface{}{"ok": false, "erro": "Senha incorreta"}); return }
	res, _ := dbUsers.Exec("DELETE FROM clientes WHERE painel = ?", painel); n, _ := res.RowsAffected(); invalidarAuthCache(); json.NewEncoder(w).Encode(map[string]interface{}{"ok": true, "deletados": n})
}

func reResolveWebPlayers() {
	data, err := os.ReadFile(".env"); if err != nil { return }
	var novos []string
	for _, line := range strings.Split(string(data), "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(strings.ToUpper(line), "WEBPLAYER") {
			if p := strings.SplitN(line, "=", 2); len(p) == 2 {
				for _, item := range strings.Split(p[1], ",") {
					item = strings.TrimSpace(item); if item == "" { continue }
					if !isIPAddress(item) { ips, err := net.LookupHost(item); if err == nil { novos = append(novos, ips...) }; novos = append(novos, item) } else { novos = append(novos, item) }
				}
			}
		}
	}
	if len(novos) > 0 { Env.WebPlayers = novos }
}

func main() {
	os.Setenv("TZ", "America/Sao_Paulo"); time.Local, _ = time.LoadLocation("America/Sao_Paulo")

	carregarEnv()
	iniciarBancoUsuarios()
	iniciarBancoMerger()

	carregarIPsRegistrados()
	carregarIPsBloqueados()

	transporteAPI := &http.Transport{
		TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
		MaxIdleConns:        200,
		MaxIdleConnsPerHost: 50,
		MaxConnsPerHost:     100,
		IdleConnTimeout:     120 * time.Second,
		DisableCompression:  false,
		ForceAttemptHTTP2:   true, 
	}
	
	transporteVideo := &http.Transport{
		TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
		MaxIdleConns:        200,
		MaxIdleConnsPerHost: 50,
		MaxConnsPerHost:     100,
		IdleConnTimeout:     120 * time.Second,
		DisableCompression:  true,  
		ForceAttemptHTTP2:   false, 
	}

	httpClient = &http.Client{Transport: transporteAPI, Timeout: 60 * time.Second}
	clientAcelerado = &http.Client{
		Transport: &http.Transport{
			TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
			MaxIdleConns:        100,
			MaxIdleConnsPerHost: 30,
			IdleConnTimeout:     60 * time.Second,
			DisableCompression:  true,
			ForceAttemptHTTP2:   false,
		},
		Timeout:       25 * time.Second,
		CheckRedirect: func(req *http.Request, via []*http.Request) error { return http.ErrUseLastResponse },
	}
	streamClient = &http.Client{Transport: transporteVideo, Timeout: 0}

	fmt.Println("=====================================================================")
	fmt.Println("🚀 [GO IPTV SERVER — MERGER + SIGMA UNIFICADO]")
	fmt.Printf("   📺 Formato Canal: %s\n", Env.FormatoCanal)
	fmt.Printf("   🔵 Painéis Sigma: %d registrados\n", len(Env.SigmaPaineis))
	fmt.Printf("   🔗 Fontes Merger: %d\n", len(Env.Fontes))
	fmt.Printf("   🖥️  Painel Admin: http://SEU_IP/painel\n")
	fmt.Printf("   🖥️  Painel Merger: http://SEU_IP/merger\n")
	fmt.Println("=====================================================================")
	
	mostrarBancoNoTerminal()

	// ⚡ INICIA O MOTOR DOS CANAIS 24H
	go iniciarRestreamers()

	go atualizarTudo()
	go func() { for { time.Sleep(time.Duration(Env.AtualizarHoras) * time.Hour); atualizarTudo() } }()
	go limparAuthCache()
	go limparIPsExpirados()
	go monitorarIPsBloqueados()
	go func() { for { time.Sleep(10 * time.Minute); mostrarEstatisticasPaineis() } }()
	go func() { for { time.Sleep(30 * time.Minute); reResolveWebPlayers() } }()

	for _, painel := range Env.SigmaPaineis {
		path := "/" + painel
		http.HandleFunc(path+"/", sigmaHandler)
		http.HandleFunc(path, sigmaHandler)
	}

	http.HandleFunc("/player_api.php", xtreamAPIHandler)
	http.HandleFunc("/xmltv.php", xtreamAPIHandler)
	http.HandleFunc("/get.php", gerarListaM3U)

	http.HandleFunc("/stats", statsHandler)
	http.HandleFunc("/painel", painelAdminHandler)
	http.HandleFunc("/api/usuarios", apiUsuariosHandler)
	http.HandleFunc("/api/usuario/toggle", apiToggleHandler)
	http.HandleFunc("/api/usuario/delete", apiDeleteHandler)
	http.HandleFunc("/api/usuario/criar", apiCriarUsuarioHandler)
	http.HandleFunc("/api/usuario/limpar-expirados", apiDeleteExpiredHandler)
	http.HandleFunc("/api/painel/delete", apiDeletePainelHandler)

	http.HandleFunc("/merger", mergerPainelPage)
	http.HandleFunc("/merger/api/stats", mergerPainelAPIStats)
	http.HandleFunc("/merger/api/search", mergerPainelAPISearch)
	http.HandleFunc("/merger/api/duplicados", mergerPainelAPIDuplicados)
	http.HandleFunc("/merger/api/bloquear", mergerPainelAPIBloquear)
	http.HandleFunc("/merger/api/desbloquear", mergerPainelAPIDesbloquear)
	http.HandleFunc("/merger/api/bloquear_todos_duplicados", mergerPainelAPIBloquearTodosDuplicados)
	http.HandleFunc("/merger/api/desbloquear_todos_duplicados", mergerPainelAPIDesbloquearTodosDuplicados)
	http.HandleFunc("/merger/api/categorias", mergerPainelAPICategorias)
	http.HandleFunc("/merger/api/canais_cat", mergerPainelAPICanaisDaCategoria)
	http.HandleFunc("/merger/api/bloquear_cat", mergerPainelAPIBloquearCat)
	http.HandleFunc("/merger/api/desbloquear_cat", mergerPainelAPIDesbloquearCat)
	http.HandleFunc("/merger/api/editar_icone", mergerPainelAPIEditarIcone)
	http.HandleFunc("/merger/api/renomear", mergerPainelAPIRenomear)
	http.HandleFunc("/merger/api/editar_url", mergerPainelAPIEditarURL)
	http.HandleFunc("/merger/api/episodios", mergerPainelAPIEpisodios)
	http.HandleFunc("/merger/api/original_url", mergerPainelAPIOriginalURL)
	http.HandleFunc("/merger/api/server_stats", mergerPainelAPIServerStats)
	
	http.HandleFunc("/merger/api/direto_on", mergerPainelAPIDiretoOn)
	http.HandleFunc("/merger/api/direto_off", mergerPainelAPIDiretoOff)
	
	// ⚡ ROTAS NOVAS DO 24H (RESTREAMER)
	http.HandleFunc("/merger/api/24h_on", mergerPainelAPI24hOn)
	http.HandleFunc("/merger/api/24h_off", mergerPainelAPI24hOff)
	http.HandleFunc("/merger/api/24h_status", mergerPainelAPI24hStatus)

	http.HandleFunc("/", playHandler)

	server := &http.Server{Addr: PortaGo, ReadTimeout: 0, WriteTimeout: 0, IdleTimeout: 0}
	log.Fatal(server.ListenAndServe())
}
