'use strict';
// ============================================================
// XPTV js 扩展执行器 —— 让 donggua-tv 支持 db.json 里 type:3 + ext 的 csp_ 源
// (即 XPTV/TvCat 系 JS 扩展)。用 node:vm 沙箱加载远程 js, 把扩展常用的
// $fetch/jsonify/argsify 桥到本服务。网络层用原生 net/tls 实现:
//   - 直连 (默认, r2.dev / raw.githubusercontent 等)
//   - HTTP CONNECT 隧道 (走容器内 mihomo 代理, 供被墙站 huangguoai.com 使用,
//     通过 EXT_PROXY_HOSTS 白名单或 opts.proxy=true 触发)
// 这样避开容器内 axios 走代理时 TLS CONNECT 被 reset 的问题。
// ============================================================
const vm = require('vm');
const net = require('net');
const tls = require('tls');
const zlib = require('zlib');
const path = require('path');
const axios = require('axios');

const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/122.0.0.0 Safari/537.36';

const fs = require('fs');
const isInsideDocker = fs.existsSync('/.dockerenv') || fs.existsSync('/run/.containerenv');
const EXT_PROXY_HOST = process.env['EXT_PROXY_HOST'] || (isInsideDocker ? 'mihomo' : '127.0.0.1');
const EXT_PROXY_PORT = parseInt(process.env['EXT_PROXY_PORT'] || '7890', 10);
const EXT_PROXY_HOSTS = (process.env['EXT_PROXY_HOSTS'] || 'huangguoai.com,huangguo.com,raw.githubusercontent.com,github.com,githubusercontent.com')
    .split(',').map(s => s.trim().toLowerCase()).filter(Boolean);

const crypto = require('crypto');
const JS_CACHE_DIR = isInsideDocker ? '/app/js_cache' : path.join(__dirname, 'js_cache');
if (!fs.existsSync(JS_CACHE_DIR)) {
    try { fs.mkdirSync(JS_CACHE_DIR, { recursive: true }); } catch (e) { }
}

const _extScriptCache = new Map();
async function fetchExtensionScript(url, timeout = 15000) {
    if (_extScriptCache.has(url)) return _extScriptCache.get(url);

    // 1. 优先尝试本地持久化缓存
    const urlHash = crypto.createHash('md5').update(url).digest('hex');
    const localCachePath = path.join(JS_CACHE_DIR, `${urlHash}.js`);
    if (fs.existsSync(localCachePath)) {
        try {
            const diskCode = fs.readFileSync(localCachePath, 'utf8');
            if (diskCode && diskCode.length > 50) {
                _extScriptCache.set(url, diskCode);
                return diskCode;
            }
        } catch (e) { }
    }

    // 2. 网络拉取（支持 2 次重试）
    let lastErr = null;
    for (let attempt = 0; attempt < 2; attempt++) {
        try {
            const resp = await extFetchWithFallback(url, { timeout, headers: { 'User-Agent': UA } });
            const data = resp && resp.data;
            const code = typeof data === 'string' ? data : (data == null ? '' : JSON.stringify(data));
            if (code && code.length >= 50) {
                _extScriptCache.set(url, code);
                try { fs.writeFileSync(localCachePath, code, 'utf8'); } catch (e) { }
                return code;
            }
        } catch (e) {
            lastErr = e;
        }
        await new Promise(r => setTimeout(r, 400));
    }

    // 3. 兜底：如果是 huangguo，读取本地预置源码
    if (url.includes('huangguo')) {
        const fallbackPath = path.join(__dirname, 'huangguo_src.js');
        if (fs.existsSync(fallbackPath)) {
            const code = fs.readFileSync(fallbackPath, 'utf8');
            _extScriptCache.set(url, code);
            return code;
        }
    }

    throw new Error('扩展内容异常: ' + url + (lastErr ? ` (${lastErr.message})` : ''));
}

// 直连 → 代理隧道 依次尝试 (先 2.5s 极速直连尝试，超时或失败立即自动无缝切换到代理隧道，并在 50x 或网络故障时自动重试)
async function extFetchWithFallback(url, opts = {}, method = 'GET') {
    let u;
    try { u = new URL(url); } catch (e) { }
    const hostLower = u ? u.hostname.toLowerCase() : '';
    const routeMode = opts && opts.__routeMode;
    if (routeMode === 'direct') {
        return extFetch(url, Object.assign({}, opts, { proxy: false }), method);
    }
    if (routeMode === 'proxy') {
        return extFetch(url, Object.assign({}, opts, { proxy: true }), method);
    }
    const mustProxy = EXT_PROXY_HOSTS.some(h => hostLower === h || hostLower.endsWith('.' + h));
    
    if (mustProxy) {
        let proxied = await extFetch(url, Object.assign({}, opts, { proxy: true }), method);
        if (!proxied || proxied.status < 200 || proxied.status >= 500 || !proxied.data) {
            await new Promise(r => setTimeout(r, 300));
            proxied = await extFetch(url, Object.assign({}, opts, { proxy: true }), method);
        }
        return proxied;
    }

    const directTimeout = (opts && opts.timeout) ? Math.min(opts.timeout, 2500) : 2500;
    const direct = await extFetch(url, Object.assign({}, opts, { proxy: false, timeout: directTimeout }), method);
    if (direct && direct.data != null && direct.status >= 200 && direct.status < 400) return direct;

    let proxied = await extFetch(url, Object.assign({}, opts, { proxy: true }), method);
    if (!proxied || proxied.status < 200 || proxied.status >= 500 || !proxied.data) {
        await new Promise(r => setTimeout(r, 300));
        proxied = await extFetch(url, Object.assign({}, opts, { proxy: true }), method);
    }
    return proxied;
}

function safeJsonify(o) {
    if (o === null || o === undefined) return o;
    if (typeof o === 'string') {
        try { return JSON.parse(o); } catch (e) { return o; }
    }
    try { return JSON.parse(JSON.stringify(o)); } catch (e) { return {}; }
}

function safeArgsify(o) {
    if (typeof o === 'string') {
        try { return JSON.parse(o); } catch (e) { return {}; }
    }
    return o || {};
}

function extJoinQuery(path, query) {
    if (!query) return path;
    let qs = '';
    if (typeof query === 'string') qs = query;
    else if (query instanceof URLSearchParams) qs = query.toString();
    else if (query && typeof query === 'object') {
        const sp = new URLSearchParams();
        for (const k of Object.keys(query)) {
            const v = query[k];
            if (Array.isArray(v)) v.forEach(x => sp.append(k, x));
            else if (v !== undefined && v !== null) sp.append(k, v);
        }
        qs = sp.toString();
    }
    return qs ? (path.includes('?') ? path + '&' + qs : path + '?' + qs) : path;
}

function extDechunk(buf) {
    const out = [];
    let i = 0;
    while (i < buf.length) {
        const eol = buf.indexOf('\r\n', i);
        if (eol === -1) break;
        const sizeLine = buf.toString('latin1', i, eol).split(';')[0].trim();
        const size = parseInt(sizeLine, 16);
        if (isNaN(size) || size <= 0) break;
        const start = eol + 2;
        if (start + size > buf.length) break;
        out.push(buf.slice(start, start + size));
        i = start + size + 2;
    }
    return Buffer.concat(out);
}

function makeCaseInsensitiveHeaders(headers) {
    return new Proxy(headers || {}, {
        get(target, prop) {
            if (typeof prop !== 'string') return target[prop];
            const pLower = prop.toLowerCase();
            for (const k of Object.keys(target)) {
                if (k.toLowerCase() === pLower) return target[k];
            }
            return undefined;
        }
    });
}

function extParseBody(headers, buf) {
    const ce = (headers['content-encoding'] || '').toLowerCase();
    let b = buf;
    if (ce.includes('gzip')) { try { b = zlib.gunzipSync(b); } catch (e) {} }
    else if (ce.includes('deflate')) { try { b = zlib.inflateSync(b); } catch (e) {} }
    else if (ce.includes('br')) { try { b = zlib.brotliDecompressSync(b); } catch (e) {} }
    return b.toString('utf8');
}

async function extFetch(url, opts = {}, method = 'GET') {
    // 跟随 3xx 重定向（部分站点根域名 301/307 跳转到带尾斜杠或新域名），最多 4 跳
    let current = url;
    for (let hop = 0; hop < 4; hop++) {
        const resp = await extFetchRaw(current, opts, method);
        const loc = resp.headers && (resp.headers['location'] || resp.headers['Location']);
        if (resp.status >= 300 && resp.status < 400 && loc) {
            try { current = new URL(loc, current).toString(); continue; }
            catch (e) { return resp; }
        }
        return resp;
    }
    return { status: 0, headers: {}, data: null, error: 'too many redirects' };
}

async function extFetchRaw(url, opts = {}, method = 'GET') {
    let u;
    try { u = new URL(url); } catch (e) { return { status: 0, headers: {}, data: null, error: 'bad url' }; }
    const hostname = u.hostname;
    const port = u.port ? parseInt(u.port, 10) : (u.protocol === 'https:' ? 443 : 80);
    const isHttps = u.protocol === 'https:';
    const timeout = (opts && opts.timeout) || 15000;

    const headers = Object.assign({}, (opts && opts.headers) || {});
    headers['User-Agent'] = headers['User-Agent'] || 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/122.0.0.0 Safari/537.36';
    headers['Accept'] = headers['Accept'] || 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8';
    headers['Host'] = hostname + (port !== (isHttps ? 443 : 80) ? ':' + port : '');
    headers['Connection'] = 'close';

    let bodyBuf = null;
    if (opts && opts.data !== undefined) {
        let body;
        if (typeof opts.data === 'string') body = opts.data;
        else { try { body = JSON.stringify(opts.data); } catch (e) { body = String(opts.data); } }
        bodyBuf = Buffer.from(body, 'utf8');
        headers['Content-Length'] = String(Buffer.byteLength(body));
        headers['Content-Type'] = headers['Content-Type'] || 'application/x-www-form-urlencoded';
    }

    // 代理决策
    const hostLower = hostname.toLowerCase();
    const forceDirect = opts && opts.proxy === false;
    const forceProxy = opts && opts.proxy === true;
    const autoProxy = !forceDirect && EXT_PROXY_HOSTS.some(h => hostLower === h || hostLower.endsWith('.' + h));
    const useProxy = forceProxy || autoProxy;

    const path = extJoinQuery(u.pathname, opts && opts.query) + (u.search || '');

    return new Promise((resolve) => {
        const timer = setTimeout(() => resolve({ status: 0, headers: {}, data: null, error: 'timeout' }), timeout);
        let settled = false;
        const done = (r) => { if (settled) return; settled = true; clearTimeout(timer); resolve(r); };

        function handle(sock, preLeftover) {
            let reqHead = `${method || 'GET'} ${path} HTTP/1.1\r\n`;
            for (const k of Object.keys(headers)) reqHead += `${k}: ${headers[k]}\r\n`;
            reqHead += '\r\n';
            let frame = Buffer.from(reqHead, 'utf8');
            if (bodyBuf) frame = Buffer.concat([frame, bodyBuf]);
            sock.write(frame);
            sock.setTimeout(timeout, () => { try { sock.destroy(); } catch (e) {} done({ status: 0, headers: {}, data: null, error: 'socket timeout' }); });
            sock.on('error', (e) => done({ status: 0, headers: {}, data: null, error: e.code || e.message }));

            let acc = preLeftover || Buffer.alloc(0);
            let headDone = false;
            const hmap = {};
            const onData = (d) => {
                if (settled) return;
                if (!headDone) {
                    acc = Buffer.concat([acc, d]);
                    const idx = acc.indexOf('\r\n\r\n');
                    if (idx === -1) return;
                    headDone = true;
                    const headRaw = acc.slice(0, idx).toString('latin1');
                    acc = acc.slice(idx + 4);
                    const lines = headRaw.split('\r\n');
                    const m = (lines.shift() || '').match(/^HTTP\/1\.\d\s+(\d+)/);
                    hmap['_status'] = m ? parseInt(m[1], 10) : 0;
                    for (const l of lines) { const c = l.indexOf(':'); if (c > -1) { const k = l.slice(0, c).trim().toLowerCase(); hmap[k] = l.slice(c + 1).trim(); } }
                } else {
                    acc = Buffer.concat([acc, d]);
                }
                const te = (hmap['transfer-encoding'] || '').toLowerCase();
                const cl = hmap['content-length'] ? parseInt(hmap['content-length'], 10) : -1;
                if (te.includes('chunked')) {
                    if (/0\r\n\r\n$/.test(acc.toString('latin1'))) finish();
                } else if (cl >= 0) {
                    if (acc.length >= cl) finish();
                } else if (headDone) {
                    // 无 length 无 chunked: 等 end
                }
            };
            sock.on('data', onData);
            sock.on('end', finish);
            sock.on('close', finish);

            function finish() {
                if (settled || !headDone) return;
                let body = Buffer.alloc(0);
                const te = (hmap['transfer-encoding'] || '').toLowerCase();
                const cl = hmap['content-length'] ? parseInt(hmap['content-length'], 10) : -1;
                if (te.includes('chunked')) body = extDechunk(acc);
                else if (cl >= 0) body = acc.slice(0, Math.min(cl, acc.length));
                else body = acc;
                const status = hmap['_status'] || 0;
                const data = extParseBody(hmap, body);
                const ciHeaders = makeCaseInsensitiveHeaders(hmap);
                done({ status, headers: ciHeaders, data, error: status >= 200 && status < 300 ? undefined : (status ? 'http ' + status : 'no response'), usedProxy: useProxy });
            }
        }

        if (useProxy) {
            const conn = net.connect(EXT_PROXY_PORT, EXT_PROXY_HOST);
            const ct = setTimeout(() => { try { conn.destroy(); } catch (e) {} done({ status: 0, headers: {}, data: null, error: 'proxy connect timeout' }); }, timeout);
            conn.on('connect', () => {
                clearTimeout(ct);
                conn.write(`CONNECT ${hostname}:${port} HTTP/1.1\r\nHost: ${hostname}:${port}\r\nProxy-Connection: keep-alive\r\n\r\n`);
            });
            let pbuf = Buffer.alloc(0);
            conn.on('data', (d) => {
                pbuf = Buffer.concat([pbuf, d]);
                const idx = pbuf.indexOf('\r\n\r\n');
                if (idx === -1) return;
                conn.removeAllListeners('data');
                const headLine = pbuf.slice(0, pbuf.indexOf('\r\n')).toString('latin1');
                if (!/^HTTP\/1\.\d\s+2/.test(headLine)) {
                    done({ status: 0, headers: {}, data: null, error: 'proxy reject: ' + headLine });
                    conn.destroy();
                    return;
                }
                const leftover = pbuf.slice(idx + 4);
                if (isHttps) {
                    const ts = tls.connect({ socket: conn, servername: hostname, rejectUnauthorized: false });
                    ts.on('secureConnect', () => handle(ts, leftover));
                    ts.on('error', (e) => done({ status: 0, headers: {}, data: null, error: 'tls ' + (e.code || e.message) }));
                } else {
                    handle(conn, leftover);
                }
            });
            conn.on('error', (e) => done({ status: 0, headers: {}, data: null, error: 'proxy ' + (e.code || e.message) }));
        } else {
            if (isHttps) {
                const ts = tls.connect({ host: hostname, port, servername: hostname, rejectUnauthorized: false });
                ts.on('secureConnect', () => handle(ts));
                ts.on('error', (e) => done({ status: 0, headers: {}, data: null, error: 'tls ' + (e.code || e.message) }));
            } else {
                const s = net.connect(port, hostname);
                s.on('connect', () => handle(s));
                s.on('error', (e) => done({ status: 0, headers: {}, data: null, error: 'net ' + (e.code || e.message) }));
            }
        }
    });
}

let _CryptoJS = null;
let _cheerio = null;
let _iconv = null;

try { _CryptoJS = require('crypto-js'); } catch (e) {
    try { _CryptoJS = require('/app/custom_modules/crypto-js'); } catch (e2) {
        try { _CryptoJS = require('/root/docker/dongguatv/node_modules/crypto-js'); } catch (e3) { }
    }
}
try { _cheerio = require('cheerio'); } catch (e) {
    try { _cheerio = require('/app/custom_modules/cheerio'); } catch (e2) {
        try { _cheerio = require('/root/docker/dongguatv/node_modules/cheerio'); } catch (e3) { }
    }
}
try { _iconv = require('iconv-lite'); } catch (e) {
    try { _iconv = require('/app/custom_modules/iconv-lite'); } catch (e2) {
        try { _iconv = require('/root/docker/dongguatv/node_modules/iconv-lite'); } catch (e3) { }
    }
}

function stubbedRequire(name) {
    if (name === 'crypto-js') return _CryptoJS;
    if (name === 'cheerio') return _cheerio;
    if (name === 'iconv-lite') return _iconv;
    return { __noop: true, __name: name };
}

const _xptvCache = new Map();
const $cache = {
    get: (k) => _xptvCache.get(String(k)),
    set: (k, v) => _xptvCache.set(String(k), v),
    remove: (k) => _xptvCache.delete(String(k)),
    delete: (k) => _xptvCache.delete(String(k)),
    clear: () => _xptvCache.clear()
};

function makeDualArg(obj) {
    if (!obj || typeof obj !== 'object') return obj;
    const jsonStr = JSON.stringify(obj);
    const dual = Array.isArray(obj) ? [...obj] : Object.assign({}, obj);
    Object.defineProperty(dual, 'toString', { value: () => jsonStr, enumerable: false, configurable: true });
    Object.defineProperty(dual, Symbol.toPrimitive, { value: () => jsonStr, enumerable: false, configurable: true });
    return dual;
}

const _compiledScriptCache = new Map();
function getCompiledExtensionScript(url, code) {
    const cached = _compiledScriptCache.get(url);
    if (cached && cached.code === code) return cached.script;
    const script = new vm.Script(code, { filename: url, displayErrors: true });
    _compiledScriptCache.set(url, { code, script });
    return script;
}

async function runExtJs(site, fnName, args, runOptions = {}) {
    const code = await fetchExtensionScript(site.ext);
    const dualArgs = makeDualArg(args);
    const routeMode = runOptions.routeMode || '';
    const routedFetch = (url, o, method) => extFetchWithFallback(url, Object.assign({}, o || {}, routeMode ? { __routeMode: routeMode } : {}), method);
    const sandbox = {
        console, Buffer, process: { env: {}, platform: 'linux' },
        setTimeout, clearTimeout, setInterval, clearInterval,
        JSON, Math, Date, RegExp, String, Number, Boolean, Array, Object,
        parseInt, parseFloat, encodeURIComponent, decodeURIComponent, isNaN, isFinite,
        URL, URLSearchParams,
        atob: (s) => Buffer.from(String(s || ''), 'base64').toString('binary'),
        btoa: (s) => Buffer.from(String(s || ''), 'binary').toString('base64'),
        createCryptoJS: () => _CryptoJS,
        CryptoJS: _CryptoJS,
        createCheerio: () => _cheerio,
        cheerio: _cheerio,
        createIconv: () => _iconv,
        iconv: _iconv,
        require: stubbedRequire,
        $cache,
        $print: (...args) => console.log(...args),
        $config: {},
        $config_str: '',
        $panel: {},
        $render: (str) => str,
        $utils: {},
        $environment: { platform: 'ios', version: '1.0.0' },
        $html: (content) => _cheerio.load(content || ''),
        $fetch: {
            get: async (url, o) => routedFetch(url, o, 'GET'),
            post: async (url, o) => routedFetch(url, o, 'POST'),
        },
        $get: async (url, o) => routedFetch(url, o, 'GET'),
        $post: async (url, o) => routedFetch(url, o, 'POST'),
        requst: async (url, o) => routedFetch(url, o, 'GET'),
        request: async (url, o) => routedFetch(url, o, 'GET'),
        http: async (url, o) => routedFetch(url, o, 'GET'),
        jsonify: safeJsonify,
        argsify: safeArgsify,
        fetchHtml: async (url, o) => {
            const resp = await routedFetch(url, o, 'GET');
            return resp && resp.data;
        }
    };
    try {
        vm.createContext(sandbox);
        getCompiledExtensionScript(site.ext, code).runInContext(sandbox, { timeout: 15000 });
        if (typeof sandbox[fnName] !== 'function') {
            throw new Error(`csp 脚本缺少函数 ${fnName}()`);
        }
        const result = await Promise.race([
            Promise.resolve(sandbox[fnName](dualArgs)),
            new Promise((_, rej) => setTimeout(() => rej(new Error(fnName + ' 超时 25s')), 25000)),
        ]);
        return safeJsonify(result);
    } catch (e) {
        throw new Error(`[${fnName}] ${e.message}`);
    }
}

function isExtSite(site) {
    return !!(site && (site.type === 3 || site.type === '3') && site.ext);
}

// 把 getTracks 的 tracks 转成前端 vod_play_url 格式 (#分隔)
function extTracksToPlayUrl(tracks) {
    if (!tracks || !tracks.length) return '';
    const parts = [];
    for (const t of tracks) {
        const name = t.name || '第1集';
        const url = t.ext && (t.ext.url || t.ext.play_url);
        if (!url) continue;
        parts.push(`${name}$${url}`);
    }
    return parts.join('#');
}

// 把 getPlayinfo 的 urls 转成可播放的直链 (优先 m3u8)
function extPlayinfoToVodUrl(playinfo) {
    if (!playinfo) return '';
    let urls = [];
    if (Array.isArray(playinfo.urls) && playinfo.urls.length) {
        urls = playinfo.urls;
    } else if (typeof playinfo.urls === 'string' && playinfo.urls) {
        urls = [playinfo.urls];
    } else if (typeof playinfo === 'string' && playinfo) {
        urls = [playinfo];
    }
    for (const u of urls) {
        // 条目可能是字符串, 也可能是 {url:,name:,...}
        const s = typeof u === 'string' ? u : (u && (u.url || u.playurl || u.play_url)) || '';
        if (s && String(s).includes('.m3u8')) return String(s);
    }
    const first = urls[0];
    return typeof first === 'string' ? first : (first && (first.url || first.playurl || first.play_url)) || '';
}

// 搜索: 内部封装 runExtJs('search', args)
async function extSearch(site, keyword) {
    const r = await runExtJs(site, 'search', { text: keyword, wd: keyword });
    const list = (r && r.list) || [];
    return list.map(item => ({
        vod_id: String(item.vod_id || item.id || '').replace(/^.*\//, ''),
        vod_name: item.vod_name || item.name || '',
        vod_pic: item.vod_pic || '',
        vod_play_url: item.vod_play_url || '',
        vod_remarks: item.vod_remarks || '',
        vod_year: item.vod_year || '',
        type_name: item.type_name || '',
        vod_content: item.vod_content || '',
        vod_play_from: item.vod_play_from || '',
        ext: item.ext || {},
    }));
}

module.exports = { extFetch, fetchExtensionScript, runExtJs, isExtSite, safeJsonify, extParseBody, extTracksToPlayUrl, extPlayinfoToVodUrl, extSearch };