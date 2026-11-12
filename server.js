// Vercel 环境会自动注入环境变量，无需加载 .env 文件
if (!process.env.VERCEL) {
    require('dotenv').config();
}

const express = require('express');
const axios = require('axios');
const bodyParser = require('body-parser');
const cors = require('cors');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const stream = require('stream');
const { promisify } = require('util');
const pipeline = promisify(stream.pipeline);

// ============ XPTV js 扩展执行器 (支持 db.json 里 type:3 + ext 的 csp_ 源) ============
// 独立模块: executor.js (原生 net/tls CONNECT 隧道访问, 避开容器内 axios 代理 TLS 问题)
const { extFetch, runExtJs, isExtSite, extTracksToPlayUrl, extPlayinfoToVodUrl, extSearch } = require('./executor');

// 媒体代理连接池：复用 TCP/TLS 连接，降低每个分片/清单请求的握手成本，
// 对“首帧”与“连播分片”的速度有明显提升。
const httpMod = require('http');
const httpsMod = require('https');
const extMediaHttpAgent = new httpMod.Agent({ keepAlive: true, maxSockets: 96, maxFreeSockets: 48, keepAliveMsecs: 8000, timeout: 30000 });
const extMediaHttpsAgent = new httpsMod.Agent({ keepAlive: true, maxSockets: 96, maxFreeSockets: 48, keepAliveMsecs: 8000, timeout: 30000, rejectUnauthorized: false });

// ========== 🔌 出网连接池硬限制(全站可用性的保命阀) ==========
// 事故(2026-08,v1.1.174):Node 默认 globalAgent.maxSockets = Infinity。前端每开一部剧就对 50+ 资源站
//   并发测速/搜索,曾有一版 /api/check 还会逐站真拉 m3u8——出网连接无上限增长,超时/中止的 socket 未及时
//   回收,累积撞穿容器 fd 上限(ulimit -n 通常 1024)后【所有新出网请求全部失败】:资源站、TMDB、弹幕、
//   甚至连自家 Cloudflare Worker 都连不上,而缓存接口照常返回 → 表现为"搜索全 0 / 资源站全灭",极难自诊断。
//   (泄漏源已删,但进程不重启则已泄漏的 fd 不释放——这正是"播放修好了搜索还坏"的原因。)
// 修:全局 Agent 显式限流 + keepAlive 复用连接(同一资源站多次请求复用同一条 TCP,fd 占用降一个数量级),
//   并设 socket 空闲超时,任何路径的泄漏都被 maxSockets 挡在天花板下,永远不会再撞穿 fd 上限。
const http = require('http');
const https = require('https');
const AGENT_OPTS = { keepAlive: true, keepAliveMsecs: 15000, maxSockets: 96, maxFreeSockets: 32, timeout: 30000, scheduling: 'lifo' };
http.globalAgent = new http.Agent(AGENT_OPTS);
https.globalAgent = new https.Agent(AGENT_OPTS);
axios.defaults.httpAgent = http.globalAgent;
axios.defaults.httpsAgent = https.globalAgent;
// 🩺 出网健康自检:fd 逼近上限时明确告警(而不是让全站静默变成"搜不到")
setInterval(() => {
    try {
        const n = (https.globalAgent.sockets ? Object.values(https.globalAgent.sockets).reduce((a, b) => a + b.length, 0) : 0)
            + (http.globalAgent.sockets ? Object.values(http.globalAgent.sockets).reduce((a, b) => a + b.length, 0) : 0);
        if (n >= AGENT_OPTS.maxSockets * 0.9) console.warn(`[出网告警] 活跃 socket ${n}/${AGENT_OPTS.maxSockets} 接近上限——上游普遍变慢或出网受阻`);
    } catch (e) { }
}, 60000).unref();

// 相对 URL 补全为绝对地址：部分源（如 lmm85）返回 "/play/xxx.html" 这类相对链接，
// 用来源详情页 URL 作为基准拼接，避免后续解析/代理因为缺 host 而失败。
function absoluteExtUrl(u, base) {
    if (!u) return '';
    if (typeof u !== 'string') return u;
    if (u.startsWith('//')) return 'https:' + u;
    if (u.startsWith('/') && base) {
        try { return new URL(u, base).toString(); } catch (e) { }
    }
    return u;
}

// 少数源返回相对链接且卡片未带详情页 URL 时，按站点主键回退到对应域名补全 host。
const EXT_BASE_HOSTS = {
    'lmm85': 'https://www.lmm85.com',
    'llmm85': 'https://www.lmm85.com',
    'jianpian': 'https://www.7fxzx.top',
    '7sefun': 'https://www.7sefun.top',
    'wwgz': 'https://vip.wwgz.cn',
    'ai': 'https://yg.giririlove.com',
    'anime1': 'https://anime1.me'
};
// =============================================================================

function isNsfwSite(site) {
    if (!site) return false;
    if (site.nsfw === true) return true;
    const key = String(site.key || '').toLowerCase();
    const api = String(site.api || '').toLowerCase();
    return key === 'huangguo' || api.startsWith('csp_huangguo');
}

function truthyFlag(v) {
    return v === true || v === 1 || v === '1' || v === 'true';
}

const app = express();

// 🎌 Kazumi 规则源(七色番/动漫巴士等 HTML 刮削站,规则格式效仿 Predidit/Kazumi):共享模块 lib/kazumi,
//    server.js 与 Vercel api/index.js 共用同一份实现(不再重蹈弹幕匹配"两处手抄、改一处漏一处"的覆辙)。
//    模块加载失败(如部署时缺 parse5 依赖)只禁用这批源,绝不拖垮主站;KAZUMI_DISABLE=1 可整体关闭。
let kazumi = null;
try { kazumi = require('./lib/kazumi'); } catch (e) { console.warn('[Kazumi] 模块加载失败,规则源已禁用:', e.message); }
// 🏷️ 资源站档案(clean/noburn/insert/unknown/ads 档位 + 分辨率 + 海外受限;前端显示 无广告/有插播/未评测/有水印):共享模块 lib/site-profiles(api/index.js 同一份)。
//    只用于前端徽章与"同一可达档内"的选源偏好;加载失败/查询抛错只是不带徽章,绝不影响搜索与播放。
let siteProfiles = null;
try { siteProfiles = require('./lib/site-profiles'); } catch (e) { console.warn('[SiteProfiles] 模块加载失败,线路徽章已禁用:', e.message); }
function profOf(site) {
    if (!siteProfiles) return undefined;   // undefined → JSON 里直接没有 site_profile 字段,前端回退 /api/sites 的 profiles 表
    try { return siteProfiles.profileFor(site); } catch (e) { return undefined; }
}
// /api/sites 附带的 {key: 档案} 表(含内置规则站)。返回新对象,绝不改 remoteDbCache/db.json 读出的原对象
function withSiteProfiles(sitesData) {
    if (!siteProfiles || !sitesData || typeof sitesData !== 'object') return sitesData;
    try {
        const base = Array.isArray(sitesData.sites) ? sitesData.sites : [];
        return Object.assign({}, sitesData, { profiles: siteProfiles.profileMap(withKzSites(base)), profiles_version: siteProfiles.version });
    } catch (e) { console.warn('[SiteProfiles] profileMap 失败,本次不带徽章:', e.message); return sitesData; }
}
// 站点全集 = db.json/远程配置的 maccms 站 + 内置 Kazumi 规则站(db.json 里同 key 的条目优先,便于覆盖/停用)
function allSites() { return withKzSites(((getDB() || {}).sites) || []); }
function withKzSites(base) {
    if (!kazumi) return base;
    let kz = [];
    try { kz = kazumi.getSites(); } catch (e) { console.warn('[Kazumi] getSites 失败,本次只用 maccms 站:', e.message); }
    const have = new Set(base.map(x => x.key));
    return base.concat(kz.filter(x => !have.has(x.key)));
}
const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(__dirname, 'db.json');
const TEMPLATE_FILE = path.join(__dirname, 'db.template.json');

// 图片缓存目录 (仅本地/Docker 环境)
const IMAGE_CACHE_DIR = path.join(__dirname, 'public/cache/images');
const EXT_IMAGE_CACHE_DIR = path.join(IMAGE_CACHE_DIR, 'ext');
if (!process.env.VERCEL && !fs.existsSync(IMAGE_CACHE_DIR)) {
    fs.mkdirSync(IMAGE_CACHE_DIR, { recursive: true });
}
if (!process.env.VERCEL && !fs.existsSync(EXT_IMAGE_CACHE_DIR)) {
    fs.mkdirSync(EXT_IMAGE_CACHE_DIR, { recursive: true });
}

// 访问密码配置（支持多密码）
// 格式：ACCESS_PASSWORD=password1 或 ACCESS_PASSWORD=password1,password2,password3
const ACCESS_PASSWORD_RAW = process.env['ACCESS_PASSWORD'] || '';
const ACCESS_PASSWORDS = ACCESS_PASSWORD_RAW ? ACCESS_PASSWORD_RAW.split(',').map(p => p.trim()).filter(p => p) : [];

// 第一个密码的哈希（兼容旧逻辑）
const PASSWORD_HASH = ACCESS_PASSWORDS.length > 0
    ? crypto.createHash('sha256').update(ACCESS_PASSWORDS[0]).digest('hex')
    : '';

// 生成密码到哈希的映射（用于历史同步）
// ⚠️ 必须无原型:普通 {} 上 PASSWORD_HASH_MAP['constructor'] / ['__proto__'] / ['toString'] 都是真值,
//    passwordHash:'constructor' 就能通过 /api/auth/verify 和各接口的 !PASSWORD_HASH_MAP[token] 校验(审查实锤)
const PASSWORD_HASH_MAP = Object.create(null);
ACCESS_PASSWORDS.forEach((pwd, index) => {
    const hash = crypto.createHash('sha256').update(pwd).digest('hex');
    PASSWORD_HASH_MAP[hash] = {
        index: index,
        // 第一个密码不启用同步（保持现有设计），其他密码启用同步
        syncEnabled: index > 0
    };
});

console.log(`[System] Password mode: ${ACCESS_PASSWORDS.length > 1 ? 'Multi-user' : 'Single'} (${ACCESS_PASSWORDS.length} passwords)`);

// 🎟️ 分享链接试看:没登录的人打开分享链接(?play=)先能看这么久(按每部剧在本机累计),到点再要求登录。0 = 关(直接锁定要登录)
//   只是前端的软门槛:搜索 / 详情接口本来就不校验令牌,登录墙一直是前端拦的
const SHARE_TRIAL_SEC = (() => {
    const raw = process.env.SHARE_TRIAL_MINUTES;
    const m = (raw === undefined || String(raw).trim() === '') ? 5 : Number(raw);
    return Number.isFinite(m) && m > 0 ? Math.round(Math.min(m, 120) * 60) : 0;
})();

// 反查：token(=SHA256(独立密码)) → 原始独立密码。仅用于站长后台辨认"是哪个独立密码用户"。
// 只在 ADMIN_TOKEN 鉴权后的后台接口里用到，不外泄。
const HASH_TO_PASSWORD = Object.create(null);
ACCESS_PASSWORDS.forEach(pwd => { HASH_TO_PASSWORD[crypto.createHash('sha256').update(pwd).digest('hex')] = pwd; });
// 求片/统计后台展示用：把 token 翻成人能认的身份
function userIdentity(token, label) {
    if (label && String(label).trim()) return String(label).trim();
    if (token && HASH_TO_PASSWORD[token]) return ((PASSWORD_HASH_MAP[token] && PASSWORD_HASH_MAP[token].index === 0) ? '主密码: ' : '独立密码: ') + HASH_TO_PASSWORD[token];
    if (token && String(token).startsWith('v2board_')) return 'v2board用户#' + String(token).slice(8, 16);
    return (token ? String(token).slice(0, 12) : '匿名');
}

// 远程配置URL
const REMOTE_DB_URL = process.env['REMOTE_DB_URL'] || '';
// 远程配置 URL 的代理（r2.dev 等需代理访问的地址；未设置则不代理）
const REMOTE_DB_PROXY = process.env['REMOTE_DB_PROXY'] || '';

// CORS 代理 URL（用于中转无法直接访问的资源站 API）
// 支持配多个(逗号/空格分隔)做冗余:CORS_PROXY_URL=https://cors.a.com,https://cors.b.com
//   每个都归一化(trim + 去尾部斜杠,拼接时统一 `${u}/?url=`)。CORS_PROXY_URL 取第一个作主代理,
//   所有历史单代理代码零改动照常用;完整列表经 /api/config 下发前端,前端在过滤代理故障时自动轮换到备用。
const CORS_PROXY_URLS = (process.env['CORS_PROXY_URL'] || '')
    .split(/[,\s]+/).map(s => s.trim().replace(/\/+$/, '')).filter(s => /^https?:\/\//i.test(s));
const CORS_PROXY_URL = CORS_PROXY_URLS[0] || '';

// 📺 直播(IPTV)：上游 M3U 源(vbskycn/iptv，每6h更新)。可用 LIVE_M3U_URL 覆盖主源、LIVE_M3U_FALLBACK 覆盖备源；
//    设 LIVE_TV_DISABLED=1 整体关闭(前端隐藏直播区、后端 /api/live/channels 返回 enabled:false)。
const LIVE_M3U_URL = process.env['LIVE_M3U_URL'] || 'https://live.zbds.top/tv/iptv4.m3u';
const LIVE_M3U_FALLBACK = process.env['LIVE_M3U_FALLBACK'] || 'https://gh-proxy.com/raw.githubusercontent.com/vbskycn/iptv/refs/heads/master/tv/iptv4.m3u';
// 第二上游(iptv-org cn)：补 CDN 域名源——vbskycn 的 CCTV 多是运营商 IP(封 Cloudflare 放不了)，iptv-org 有 cctvplus 等 CDN 源。
const LIVE_M3U_IPTVORG = process.env['LIVE_M3U_IPTVORG'] || 'https://iptv-org.github.io/iptv/countries/cn.m3u';
// 第三上游(iptv-org 中文语言表)：countries/cn 多是运营商 IP；languages/zho 反而收录大量【海外 CDN】华语源——
// CCTV-1~17 完整 + CGTN 全家(News/Doc/西/阿/俄/法,多带 ACAO:*) + CCTV-4 America/Europe/Asia + 卫视。实测海外可播的关键补充。
const LIVE_M3U_ZHO = process.env['LIVE_M3U_ZHO'] || 'https://iptv-org.github.io/iptv/languages/zho.m3u';
// 自定义上游(可选)：用户有付费 IPTV 的 m3u 可设 LIVE_M3U_EXTRA(逗号分隔多个)，并入合并 → 能播什么由它决定。
const LIVE_M3U_EXTRA = (process.env['LIVE_M3U_EXTRA'] || '').split(',').map(s => s.trim()).filter(Boolean);
// 🏀 免费 CCTV5 / CCTV5+：第三方 redirector → 咪咕(migu)源。https + ACAO:*，海外【直连】可播
//    (实测返回真 TS 分段、media-seq 实时递增，非 catvod 那种 backup 待机台)。仅这两个体育频道稳定可用——其余 /cctv/N 皆 404。
//    放在合并最前 → 与上游同名 CCTV5/CCTV5+ 归并时其 https 线路(rank0)排第一被优先播，运营商死源退为兜底。源失效用 LIVE_M3U_DISABLE 连内置一起关。
const LIVE_KAFEI_GEN = [
    { name: 'CCTV5', group: '体育', url: 'https://live.666666.zip/cctv/5.m3u8' },
    { name: 'CCTV5+', group: '体育', url: 'https://live.666666.zip/cctv/5p.m3u8' },
];
// 布尔型环境变量：0/false/no/off/空 都算"未开启"——JS 里 "0"/"false" 是 truthy，
// 用户把 LIVE_TV_DISABLED=0 当"不禁用"填时曾把整个直播关掉(线上事故:首页直播频道消失)。
const envFlag = (name) => { const v = String(process.env[name] ?? '').trim().toLowerCase(); return v !== '' && v !== '0' && v !== 'false' && v !== 'no' && v !== 'off'; };
const LIVE_TV_ENABLED = !envFlag('LIVE_TV_DISABLED');
// LIVE_M3U_DISABLE=1：关掉所有内置上游(vbskycn/iptv-org/国际/内置CCTV5源)，只用 LIVE_M3U_EXTRA 自定义源。
const LIVE_BUILTIN = !envFlag('LIVE_M3U_DISABLE');
// 后台验证：每次刷新后通过 worker(http源)/直连(https源)实测每个频道首条线路能否播，标 ok 并把能播的排前。
// 不删频道(全列出),只标记+排序。设 LIVE_NO_VALIDATE=1 关闭(纯全列出、不打 worker)。
const LIVE_VALIDATE = !envFlag('LIVE_NO_VALIDATE');

// 环境变量加载状态日志（用于 Vercel 调试）
console.log(`[System] Environment: ${process.env.VERCEL ? 'Vercel Serverless' : 'Local/VPS'}`);
console.log(`[System] TMDB_API_KEY: ${process.env.TMDB_API_KEY ? '✓ Configured' : '✗ Missing'}`);
console.log(`[System] TMDB_PROXY_URL: ${process.env['TMDB_PROXY_URL'] || '(not set)'}`);
console.log(`[System] CORS_PROXY_URL: ${CORS_PROXY_URL || '(not set)'}${CORS_PROXY_URLS.length > 1 ? ` (+${CORS_PROXY_URLS.length - 1} 备用: ${CORS_PROXY_URLS.slice(1).join(', ')})` : ''}`);
console.log(`[System] REMOTE_DB_URL: ${REMOTE_DB_URL ? '✓ Configured' : '(not set)'}`);
console.log(`[System] 直播(IPTV): ${LIVE_TV_ENABLED ? '✓ 启用 (' + LIVE_M3U_URL + ')' : '✗ 已禁用 (LIVE_TV_DISABLED)'}`);



// 远程配置缓存
let remoteDbCache = null;
let remoteDbLastFetch = 0;
const REMOTE_DB_CACHE_TTL = 5 * 60 * 1000; // 5分钟缓存

// 记录需要使用代理的站点（自动学习，带过期时间）
// 格式：{ siteKey: expireTimestamp }
const proxyRequiredSites = new Map();
const PROXY_MEMORY_TTL = 24 * 60 * 60 * 1000; // 24小时后重新尝试直连
const SLOW_THRESHOLD_MS = 1500; // 直连延迟超过此值视为慢速，尝试代理

// IP 地理位置缓存 (避免频繁调用外部 API)
const ipLocationCache = new Map();
const IP_CACHE_TTL = 3600 * 1000; // 缓存1小时

/**
 * 获取请求者的真实 IP 地址
 * 支持 Cloudflare, Nginx 等反向代理
 */
function getClientIP(req) {
    return req.headers['cf-connecting-ip'] ||  // Cloudflare
        req.headers['x-real-ip'] ||          // Nginx
        (req.headers['x-forwarded-for'] || '').split(',')[0].trim() ||
        req.socket?.remoteAddress ||
        '';
}

/**
 * HTML 转义：用于把不可信数据(如 TMDB 标题/简介)安全地插入服务端渲染的 HTML/属性，
 * 防止 XSS。覆盖 & < > " ' 五个字符。
 */
function escapeHtml(str) {
    return String(str == null ? '' : str)
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#39;');
}

/**
 * 检测是否为私有/内网 IP 地址
 * @param {string} ip - IP 地址
 * @returns {boolean} - 是否是私有 IP
 */
function isPrivateIP(ip) {
    if (!ip) return false;
    // IPv4 私有地址
    if (/^127\./.test(ip)) return true;  // 127.0.0.0/8 (loopback)
    if (/^10\./.test(ip)) return true;   // 10.0.0.0/8
    if (/^172\.(1[6-9]|2[0-9]|3[0-1])\./.test(ip)) return true;  // 172.16.0.0/12
    if (/^192\.168\./.test(ip)) return true;  // 192.168.0.0/16
    if (/^169\.254\./.test(ip)) return true;  // 169.254.0.0/16 (link-local)
    // IPv6 私有/特殊地址
    if (ip === '::1') return true;  // loopback
    if (/^fe80:/i.test(ip)) return true;  // link-local
    if (/^fc00:/i.test(ip) || /^fd[0-9a-f]{2}:/i.test(ip)) return true;  // unique local
    return false;
}

/**
 * 检测 IP 是否来自中国大陆（需要使用代理）
 * 支持从 X-Client-Public-IP 头获取客户端提供的公网 IP
 * 私有 IP 默认视为需要代理（假设部署在中国大陆内网环境）
 * @param {object} req - Express 请求对象
 * @returns {Promise<boolean>} - 是否需要使用代理
 */
async function isChineseIP(req) {
    // 1. 优先使用客户端提供的公网 IP (由前端从 api.ip.sb 获取)
    const clientProvidedIP = req.headers['x-client-public-ip'];
    // 2. 回退到服务端检测的 IP
    const detectedIP = getClientIP(req);

    // 使用客户端提供的 IP（如果有效且非私有）
    let effectiveIP = clientProvidedIP && !isPrivateIP(clientProvidedIP) ? clientProvidedIP : detectedIP;

    // 3. 如果有效 IP 仍然是私有的，直接返回 true（视为需要代理）
    if (!effectiveIP || isPrivateIP(effectiveIP)) {
        console.log(`[IP Detection] Private/LAN IP detected (${detectedIP}), treating as CN (proxy required)`);
        return true;
    }

    // 检查缓存
    const cached = ipLocationCache.get(effectiveIP);
    if (cached && (Date.now() - cached.time < IP_CACHE_TTL)) {
        return cached.isCN;
    }

    try {
        const response = await axios.get(`https://api.ip.sb/geoip/${effectiveIP}`, {
            timeout: 3000,
            headers: { 'User-Agent': 'DongguaTV/1.0' }
        });

        const data = response.data;
        // 检查是否是中国大陆 (排除港澳台)
        let isCN = false;
        if (data.country_code === 'CN') {
            const excludeRegions = ['Hong Kong', 'Macau', 'Taiwan', '香港', '澳门', '台湾'];
            const region = data.region || data.city || '';
            if (!excludeRegions.some(r => region.includes(r))) {
                isCN = true;
            }
        }

        // 缓存结果
        ipLocationCache.set(effectiveIP, { isCN, time: Date.now() });
        console.log(`[IP Detection] ${effectiveIP} -> ${isCN ? '中国大陆' : '海外'}${clientProvidedIP ? ' (client-provided)' : ''}`);
        return isCN;

    } catch (error) {
        // API 调用失败，默认不使用代理
        console.error(`[IP Detection Error] ${effectiveIP}:`, error.message);
        return false;
    }
}

/**
 * 检测字符串是否主要包含英文字符（用于判断是否需要翻译）
 * @param {string} text - 待检测文本
 * @returns {boolean} - 是否主要是英文
 */
function isMainlyEnglish(text) {
    if (!text) return false;
    // 去除空格和标点后检测
    const cleaned = text.replace(/[\s\d\-\_\:\.\,\!\?\'\"\(\)\[\]]/g, '');
    if (cleaned.length === 0) return false;

    // 计算英文字母占比
    const englishChars = (cleaned.match(/[a-zA-Z]/g) || []).length;
    const ratio = englishChars / cleaned.length;

    // 如果英文字符占比超过 70%，认为是英文
    return ratio > 0.7;
}

/**
 * 通过 TMDB 搜索获取影片的中文名称
 * 利用 TMDB 的多语言支持，查询英文标题对应的中文翻译
 * 注意：会自动使用 TMDB_PROXY_URL 代理（如果配置）
 * @param {string} englishTitle - 英文标题
 * @returns {Promise<string[]>} - 找到的中文标题数组
 */
async function fetchChineseTitleFromTMDB(englishTitle) {
    const TMDB_API_KEY = process.env.TMDB_API_KEY;
    const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];
    if (!TMDB_API_KEY) return [];

    // 构建 TMDB API 基础 URL（支持代理）
    // cloudflare-tmdb-proxy.js 需要 /api/3/ 前缀
    const TMDB_BASE = TMDB_PROXY_URL
        ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3`  // 代理需要 /api/3 前缀
        : 'https://api.themoviedb.org/3';

    try {
        // 先用英文搜索找到影片 ID
        const searchUrl = `${TMDB_BASE}/search/multi?api_key=${TMDB_API_KEY}&query=${encodeURIComponent(englishTitle)}&language=en-US`;
        const searchResponse = await axios.get(searchUrl, { timeout: 8000 });

        if (!searchResponse.data.results || searchResponse.data.results.length === 0) {
            return [];
        }

        const firstResult = searchResponse.data.results[0];
        const mediaType = firstResult.media_type;  // movie 或 tv
        const id = firstResult.id;

        if (!id || (mediaType !== 'movie' && mediaType !== 'tv')) {
            return [];
        }

        // 用中文语言获取详情，TMDB 会返回中文标题
        const detailUrl = `${TMDB_BASE}/${mediaType}/${id}?api_key=${TMDB_API_KEY}&language=zh-CN`;
        const detailResponse = await axios.get(detailUrl, { timeout: 8000 });

        const chineseTitles = [];
        const chineseTitle = detailResponse.data.title || detailResponse.data.name;

        if (chineseTitle && chineseTitle !== englishTitle) {
            chineseTitles.push(chineseTitle);
            console.log(`[TMDB Translation] "${englishTitle}" => "${chineseTitle}"`);
        }

        // 尝试获取更多别名（alternative_titles）- 使用较短超时，失败不影响主流程
        try {
            const altUrl = `${TMDB_BASE}/${mediaType}/${id}/alternative_titles?api_key=${TMDB_API_KEY}`;
            const altResponse = await axios.get(altUrl, { timeout: 5000 });

            // 电影用 titles，电视剧用 results
            const alternatives = altResponse.data.titles || altResponse.data.results || [];

            // 查找中文地区的别名 (CN, TW, HK)
            for (const alt of alternatives) {
                const country = alt.iso_3166_1;
                if (['CN', 'TW', 'HK'].includes(country) && alt.title) {
                    if (!chineseTitles.includes(alt.title) && alt.title !== englishTitle) {
                        chineseTitles.push(alt.title);
                    }
                }
            }
        } catch (e) {
            // 别名获取失败不影响主流程
        }

        return chineseTitles;
    } catch (error) {
        // 翻译失败不阻塞搜索，静默返回空数组
        if (error.code !== 'ECONNABORTED') {
            console.error(`[TMDB Translation Error] ${englishTitle}:`, error.message);
        }
        return [];
    }
}

/**
 * 智能生成搜索关键词变体
 * 用于提高搜索命中率，解决 TMDB 标题与资源站标题不匹配的问题
 * 例如："利刃出鞘3：亡者归来" -> ["利刃出鞘3：亡者归来", "利刃出鞘3", "利刃出鞘"]
 * @param {string} keyword - 原始搜索关键词
 * @param {string} originalTitle - 可选的原始标题（如英文名）
 * @returns {string[]} - 关键词变体数组（已去重）
 */
function generateSearchKeywords(keyword, originalTitle = '') {
    const keywords = new Set();

    if (!keyword) return [];

    // 1. 原始关键词
    keywords.add(keyword.trim());

    // 2. 如果有原始标题（英文名），也加入
    if (originalTitle && originalTitle.trim() && originalTitle !== keyword) {
        keywords.add(originalTitle.trim());
    }

    // 3. 去除常见分隔符后的主标题
    // 常见分隔符：：、:、-、—、·、|、/
    const separators = ['：', ':', '–', '—', '-', '·', '|', '/', '~'];
    for (const sep of separators) {
        if (keyword.includes(sep)) {
            const mainTitle = keyword.split(sep)[0].trim();
            if (mainTitle && mainTitle.length >= 2) {
                keywords.add(mainTitle);
            }
        }
    }

    // 4. 去除括号内容：《》、()、（）、【】、[]
    const bracketPatterns = [
        /《[^》]*》/g,
        /\([^)]*\)/g,
        /（[^）]*）/g,
        /\[[^\]]*\]/g,
        /【[^】]*】/g
    ];
    let cleanedKeyword = keyword;
    for (const pattern of bracketPatterns) {
        cleanedKeyword = cleanedKeyword.replace(pattern, '').trim();
    }
    if (cleanedKeyword && cleanedKeyword !== keyword && cleanedKeyword.length >= 2) {
        keywords.add(cleanedKeyword);
    }

    // 5. 对于带数字续集的影片，尝试只保留数字前面的部分
    // 例如："利刃出鞘3" -> "利刃出鞘"  (但不移除如 "007" 这样的数字标题)
    const numericMatch = keyword.match(/^(.+?)\d+$/);
    if (numericMatch && numericMatch[1] && numericMatch[1].length >= 2) {
        // 只有当前面有足够长的标题时才添加
        const baseTitle = numericMatch[1].trim();
        if (baseTitle.length >= 2) {
            keywords.add(baseTitle);
        }
    }

    // 6. 去除 "第X季"、"第X部"、"Season X" 等后缀
    const seasonPatterns = [
        /第[一二三四五六七八九十\d]+季$/,
        /第[一二三四五六七八九十\d]+部$/,
        /Season\s*\d+$/i,
        /S\d+$/i
    ];
    let noSeasonKeyword = keyword;
    for (const pattern of seasonPatterns) {
        noSeasonKeyword = noSeasonKeyword.replace(pattern, '').trim();
    }
    if (noSeasonKeyword && noSeasonKeyword !== keyword && noSeasonKeyword.length >= 2) {
        keywords.add(noSeasonKeyword);
    }

    return Array.from(keywords);
}


/**
 * 检查站点是否需要使用代理（未过期）
 */
function shouldUseProxy(siteKey) {
    if (!proxyRequiredSites.has(siteKey)) return false;
    const expireTime = proxyRequiredSites.get(siteKey);
    if (Date.now() > expireTime) {
        // 已过期，移除记录，下次会重新尝试直连
        proxyRequiredSites.delete(siteKey);
        console.log(`[Proxy Memory] ${siteKey} 代理记录已过期，将重新尝试直连`);
        return false;
    }
    return true;
}

/**
 * 标记站点需要使用代理
 */
function markSiteNeedsProxy(siteKey, reason = '') {
    const expireTime = Date.now() + PROXY_MEMORY_TTL;
    proxyRequiredSites.set(siteKey, expireTime);
    const expireDate = new Date(expireTime).toLocaleString('zh-CN');
    console.log(`[Proxy Memory] ${siteKey} 已标记为需要代理${reason ? ` (${reason})` : ''}，有效期至 ${expireDate}`);
}

/**
 * 带代理回退的请求函数
 * 先尝试直接请求，失败或太慢时通过 CORS 代理重试
 * @param {string} url - 请求 URL
 * @param {object} options - axios 配置
 * @param {string} siteKey - 站点标识（用于记忆）
 * @returns {Promise<object>} - { data, usedProxy, latency }
 */
async function fetchWithProxyFallback(url, options = {}, siteKey = '') {
    // 后台任务(收藏更新检查)走单独的分支;交互请求(/api/search、/api/detail…)下面的逻辑一字未改
    if (options && options.bg) return fetchWithProxyFallbackBg(url, options, siteKey);
    const timeout = options.timeout || 8000;

    // 如果该站点之前需要代理且未过期，直接使用代理
    if (CORS_PROXY_URL && siteKey && shouldUseProxy(siteKey)) {
        try {
            const startTime = Date.now();
            const proxyUrl = `${CORS_PROXY_URL}/?url=${encodeURIComponent(url)}`;
            const response = await axios.get(proxyUrl, { ...options, timeout });
            const latency = Date.now() - startTime;
            return { data: response.data, usedProxy: true, latency };
        } catch (proxyError) {
            // 代理也失败，移除记忆，下次重新尝试直连
            proxyRequiredSites.delete(siteKey);
            console.log(`[Proxy Fallback] ${siteKey} 代理失败，已清除记录`);
            throw proxyError;
        }
    }

    // 尝试直接请求
    const startTime = Date.now();
    try {
        const response = await axios.get(url, { ...options, timeout });
        const directLatency = Date.now() - startTime;

        // 检查是否太慢，如果配置了代理，尝试代理看是否更快
        if (CORS_PROXY_URL && directLatency > SLOW_THRESHOLD_MS) {
            console.log(`[Proxy Fallback] ${siteKey || url} 直连较慢 (${directLatency}ms)，尝试代理对比...`);

            try {
                const proxyStartTime = Date.now();
                const proxyUrl = `${CORS_PROXY_URL}/?url=${encodeURIComponent(url)}`;
                const proxyResponse = await axios.get(proxyUrl, { ...options, timeout: timeout + 2000 });
                const proxyLatency = Date.now() - proxyStartTime;

                // 如果代理更快（至少快 30%），使用代理结果并记住
                if (proxyLatency < directLatency * 0.7) {
                    console.log(`[Proxy Fallback] ${siteKey || url} 代理更快 (${proxyLatency}ms vs ${directLatency}ms)，使用代理`);
                    if (siteKey) {
                        markSiteNeedsProxy(siteKey, `代理更快: ${proxyLatency}ms vs 直连 ${directLatency}ms`);
                    }
                    return { data: proxyResponse.data, usedProxy: true, latency: proxyLatency };
                } else {
                    console.log(`[Proxy Fallback] ${siteKey || url} 直连仍更快 (${directLatency}ms vs ${proxyLatency}ms)，继续使用直连`);
                }
            } catch (proxyError) {
                // 代理失败，继续使用直连结果
                console.log(`[Proxy Fallback] ${siteKey || url} 代理测试失败，继续使用直连`);
            }
        }

        return { data: response.data, usedProxy: false, latency: directLatency };
    } catch (directError) {
        // 直接请求失败，如果配置了代理，尝试通过代理
        if (CORS_PROXY_URL) {
            try {
                console.log(`[Proxy Fallback] ${siteKey || url} 直连失败，尝试代理...`);
                const proxyStartTime = Date.now();
                const proxyUrl = `${CORS_PROXY_URL}/?url=${encodeURIComponent(url)}`;
                const response = await axios.get(proxyUrl, { ...options, timeout: timeout + 2000 });
                const proxyLatency = Date.now() - proxyStartTime;

                // 记住该站点需要代理（带过期时间）
                if (siteKey) {
                    markSiteNeedsProxy(siteKey, '直连失败');
                }

                return { data: response.data, usedProxy: true, latency: proxyLatency };
            } catch (proxyError) {
                console.error(`[Proxy Fallback] ${siteKey || url} 代理请求也失败:`, proxyError.message);
                throw proxyError;
            }
        }
        throw directError;
    }
}

// 后台批量请求版(options.bg = true):
//   · 不做"直连慢 → 再走代理比一比"(批量详情 20 个 id 响应大、本来就慢,对比一次就是多一个请求、还耗 Worker 额度);
//   · 只读、绝不写 proxyRequiredSites:后台大批量的慢/超时不能把这个站的用户搜索钉到代理 24h(或把它解钉);
//     已知要代理的站直接走代理;
//   · 直连失败仍可走一次代理,但要先 options.extra() 占一个请求预算(返回 false = 本轮预算用完,直接按失败处理)。
async function fetchWithProxyFallbackBg(url, options, siteKey) {
    const { bg, extra, ...opts } = options;
    const timeout = opts.timeout || 8000;
    const viaProxy = (t) => axios.get(`${CORS_PROXY_URL}/?url=${encodeURIComponent(url)}`, { ...opts, timeout: t });
    const until = siteKey ? proxyRequiredSites.get(siteKey) : 0;   // 只读(shouldUseProxy 会顺手删过期记录)
    if (CORS_PROXY_URL && until && until > Date.now()) {
        const r = await viaProxy(timeout);
        return { data: r.data, usedProxy: true };
    }
    try {
        const r = await axios.get(url, { ...opts, timeout });
        return { data: r.data, usedProxy: false };
    } catch (directError) {
        if (!CORS_PROXY_URL || (typeof extra === 'function' && !extra())) throw directError;
        const r = await viaProxy(timeout + 2000);
        return { data: r.data, usedProxy: true };
    }
}

// 缓存配置
const CACHE_TYPE = process.env.CACHE_TYPE || 'json'; // json, sqlite, memory, none
const SEARCH_CACHE_JSON = path.join(__dirname, 'cache_search.json');
const DETAIL_CACHE_JSON = path.join(__dirname, 'cache_detail.json');
const INTRO_CACHE_JSON = path.join(__dirname, 'cache_intro.json');
const INTRO_ENV_CACHE_JSON = path.join(__dirname, 'cache_intro_env.json');
const CACHE_DB_FILE = path.join(__dirname, 'cache.db');

console.log(`[System] Cache Type: ${CACHE_TYPE}`);

// 初始化数据库文件 (仅本地/Docker 环境)
if (!process.env.VERCEL && !fs.existsSync(DATA_FILE)) {
    if (fs.existsSync(TEMPLATE_FILE)) {
        fs.copyFileSync(TEMPLATE_FILE, DATA_FILE);
        console.log('[Init] 已从模板创建 db.json');
    } else {
        const initialData = { sites: [] };
        fs.writeFileSync(DATA_FILE, JSON.stringify(initialData, null, 2));
        console.log('[Init] 已创建默认 db.json');
    }
}

// ========== 缓存抽象层 ==========
class CacheManager {
    constructor(type) {
        this.type = type;
        this.searchCache = {};
        this.detailCache = {};
        this.introCache = {};    // ⏭️ 片头/片尾标记(json/memory 模式):独立命名空间,不与 VOD 详情缓存串味/共用淘汰
        this.introEnvCache = {}; // 🎵 片头/片尾音频响度包络(客户端学习成果的云备份,跨设备/跨线路复用)
        this.db = null;
        this.init();
        // 📈 命中频次跟踪：用于热门自适应 TTL（反复访问的剧/源自动延长缓存寿命）
        this._hits = new Map(); // key: `${category}:${key}` → count
    }

    // 🎯 热门自适应：命中时累计热度，热度到阈值就把该条缓存寿命延长。
    //    冷门条目标 minute 就过期，热门条目反复被看时持续续命——命中率上升，坏源重新拉取降频。
    _trackHit(category, key) {
        try {
            const k = `${category}:${key}`;
            const c = (this._hits.get(k) || 0) + 1;
            this._hits.set(k, c);
            if (this._hits.size > 4000) {
                const drop = [...this._hits.keys()].slice(0, 800);
                drop.forEach(dk => this._hits.delete(dk));
            }
            // 热度达到阈值时，把该条目的过期时间向后刷新（热门续命）
            if (this.type === 'sqlite' && this.db && c >= 3) {
                const row = this.db.prepare(
                    'SELECT expire FROM cache WHERE category = ? AND key = ?'
                ).get(category, key);
                if (row) {
                    const remain = row.expire - Date.now();
                    if (remain < 1800 * 1000) {  // 剩余不足 30 分钟才续，避免无意义抖动
                        const extendSec = c >= 12 ? 7200 : c >= 6 ? 3600 : 1800;
                        this.db.prepare(
                            'UPDATE cache SET expire = ? WHERE category = ? AND key = ?'
                        ).run(Date.now() + extendSec * 1000, category, key);
                    }
                }
            }
        } catch (e) { }
    }

    init() {
        if (this.type === 'json') {
            if (fs.existsSync(SEARCH_CACHE_JSON)) {
                try { this.searchCache = JSON.parse(fs.readFileSync(SEARCH_CACHE_JSON)); } catch (e) { }
            }
            if (fs.existsSync(DETAIL_CACHE_JSON)) {
                try { this.detailCache = JSON.parse(fs.readFileSync(DETAIL_CACHE_JSON)); } catch (e) { }
            }
            if (fs.existsSync(INTRO_CACHE_JSON)) {
                try { this.introCache = JSON.parse(fs.readFileSync(INTRO_CACHE_JSON)); } catch (e) { }
            }
            if (fs.existsSync(INTRO_ENV_CACHE_JSON)) {
                try { this.introEnvCache = JSON.parse(fs.readFileSync(INTRO_ENV_CACHE_JSON)); } catch (e) { }
            }
        } else if (this.type === 'sqlite') {
            try {
                const Database = require('better-sqlite3');
                this.db = new Database(CACHE_DB_FILE);

                // WAL 模式 + 自动 checkpoint：之前 DB 处于 WAL 但无自动 checkpoint，
                // WAL 文件会无限增长(已观测到 4MB)占满磁盘。这里显式开启并限制 WAL 大小。
                try {
                    this.db.pragma('journal_mode = WAL');
                    this.db.pragma('wal_autocheckpoint = 1000'); // 约累计 4MB 自动 checkpoint
                    this.db.pragma('synchronous = NORMAL');
                } catch (e) { console.warn('[Cache] 设置 WAL pragma 失败:', e.message); }

                // 创建缓存表
                this.db.exec(`
                    CREATE TABLE IF NOT EXISTS cache (
                        category TEXT NOT NULL,
                        key TEXT NOT NULL,
                        value TEXT NOT NULL,
                        expire INTEGER NOT NULL,
                        PRIMARY KEY (category, key)
                    )
                `);

                // 创建用户历史记录表（用于多用户同步）
                this.db.exec(`
                    CREATE TABLE IF NOT EXISTS user_history (
                        user_token TEXT NOT NULL,
                        item_id TEXT NOT NULL,
                        item_data TEXT NOT NULL,
                        updated_at INTEGER NOT NULL,
                        PRIMARY KEY (user_token, item_id)
                    )
                `);

                // 创建索引加速过期查询
                this.db.exec(`CREATE INDEX IF NOT EXISTS idx_expire ON cache(expire)`);
                this.db.exec(`CREATE INDEX IF NOT EXISTS idx_history_user ON user_history(user_token)`);

                // 清理过期数据
                this.db.prepare('DELETE FROM cache WHERE expire < ?').run(Date.now());

                console.log(`[SQLite Cache] Database initialized: ${CACHE_DB_FILE}`);
            } catch (e) {
                console.error('[SQLite Cache] Init failed, falling back to memory:', e.message);
                this.type = 'memory';
            }
        }
    }

    _bucket(category) { return category === 'search' ? this.searchCache : category === 'intro' ? this.introCache : category === 'introenv' ? this.introEnvCache : this.detailCache; }

    get(category, key) {
        if (this.type === 'memory') {
            const data = this._bucket(category)[key];
            if (data && data.expire > Date.now()) { this._trackHit(category, key); return data.value; }
            return null;
        } else if (this.type === 'json') {
            const data = this._bucket(category)[key];
            if (data && data.expire > Date.now()) { this._trackHit(category, key); return data.value; }
            return null;
        } else if (this.type === 'sqlite' && this.db) {
            try {
                const row = this.db.prepare(
                    'SELECT value FROM cache WHERE category = ? AND key = ? AND expire > ?'
                ).get(category, key, Date.now());
                if (row) { this._trackHit(category, key); return JSON.parse(row.value); }
                return null;
            } catch (e) {
                console.error('[SQLite Cache] Get error:', e.message);
                return null;
            }
        }
        return null;
    }

    set(category, key, value, ttlSeconds = 600) {
        const expire = Date.now() + ttlSeconds * 1000;

        if (this.type === 'memory') {
            const item = { value, expire };
            this._bucket(category)[key] = item;
        } else if (this.type === 'json') {
            const item = { value, expire };
            this._bucket(category)[key] = item;
            this.saveDisk(category);
        } else if (this.type === 'sqlite' && this.db) {
            try {
                this.db.prepare(`
                    INSERT OR REPLACE INTO cache (category, key, value, expire)
                    VALUES (?, ?, ?, ?)
                `).run(category, key, JSON.stringify(value), expire);
            } catch (e) {
                console.error('[SQLite Cache] Set error:', e.message);
            }
        }
    }

    saveDisk(only) {
        if (this.type !== 'json') return;
        // 只写被改动的桶(片头/片尾提交别每次重写整个详情缓存文件)
        if (!only || only === 'search') fs.writeFileSync(SEARCH_CACHE_JSON, JSON.stringify(this.searchCache));
        if (!only || only === 'intro') fs.writeFileSync(INTRO_CACHE_JSON, JSON.stringify(this.introCache));
        if (!only || only === 'introenv') fs.writeFileSync(INTRO_ENV_CACHE_JSON, JSON.stringify(this.introEnvCache));
        if (!only || (only !== 'search' && only !== 'intro' && only !== 'introenv')) fs.writeFileSync(DETAIL_CACHE_JSON, JSON.stringify(this.detailCache));
    }

    // 按 key 前缀列出某类别下的未过期条目(音频包络"跨线路借用"查同剧其它线路用)。上限截断防大扫描。
    list(category, prefix, limit = 20) {
        const out = [];
        if (this.type === 'memory' || this.type === 'json') {
            const bucket = this._bucket(category), now = Date.now();
            for (const k of Object.keys(bucket)) {
                if (k.indexOf(prefix) !== 0) continue;
                const data = bucket[k];
                if (data && data.expire > now) { out.push({ key: k, value: data.value }); if (out.length >= limit) break; }
            }
        } else if (this.type === 'sqlite' && this.db) {
            try {
                // LIKE 通配符注入防护:剧名归一化不会剥掉 % ,必须转义(否则含 % 的标题会匹配到别的剧)
                const esc = prefix.replace(/[\\%_]/g, ch => '\\' + ch);
                const rows = this.db.prepare(
                    "SELECT key, value FROM cache WHERE category = ? AND key LIKE ? ESCAPE '\\' AND expire > ? LIMIT ?"
                ).all(category, esc + '%', Date.now(), limit);
                for (const r of rows) { try { out.push({ key: r.key, value: JSON.parse(r.value) }); } catch (e) { } }
            } catch (e) {
                console.error('[SQLite Cache] List error:', e.message);
            }
        }
        return out;
    }

    // 定期清理过期缓存 (json/memory) + 软上限逐出 (SQLite)。
    // json / memory 模式以前从不删过期条目(get 只是不认),桶只增不减 —— 分类浏览每翻一页就是一条新的 TMDB 缓存,
    // json 还要在每次写入时把整个文件重写一遍;这里删掉过期的,json 有删才落一次盘。
    // SQLite: 除删除过期条目外,每类缓存设置软上限,超出时按"到期时间最远→最久未用"优先淘汰,防止 DB 无限膨胀
    // (尤其 search/detail 长期累积),同时热门条目因 TTL 续命而天然保留更久。
    cleanup() {
        if (this.type === 'memory' || this.type === 'json') {
            const now = Date.now();
            for (const cat of ['search', 'detail', 'intro', 'introenv']) {
                const bucket = this._bucket(cat);
                let removed = 0;
                for (const k of Object.keys(bucket)) {
                    const d = bucket[k];
                    if (!d || !(d.expire > now)) { delete bucket[k]; removed++; }
                }
                if (removed && this.type === 'json') {
                    try { this.saveDisk(cat); } catch (e) { console.error('[Cache] Save after cleanup failed:', e.message); }
                }
            }
            return;
        }
        if (this.type === 'sqlite' && this.db) {
            try {
                const result = this.db.prepare('DELETE FROM cache WHERE expire < ?').run(Date.now());
                if (result.changes > 0) {
                    console.log(`[SQLite Cache] Cleaned ${result.changes} expired entries`);
                }
                // 软上限：按类别逐出超量条目（最久未过期 / 最小评估保留价值优先淘汰）
                const limits = { detail: 8000, search: 6000, ext_media: 3000 };
                for (const [cat, limit] of Object.entries(limits)) {
                    try {
                        const row = this.db.prepare(
                            'SELECT COUNT(*) AS c FROM cache WHERE category = ?'
                        ).get(cat);
                        if (row && row.c > limit) {
                            const over = row.c - limit;
                            const removed = this.db.prepare(`
                                DELETE FROM cache WHERE category = ? AND key IN (
                                    SELECT key FROM cache WHERE category = ?
                                    ORDER BY expire ASC LIMIT ?
                                )
                            `).run(cat, cat, over);
                            if (removed.changes > 0) {
                                console.log(`[SQLite Cache] 软上限淘汰 ${cat}: 移除 ${removed.changes} 条(现 ${row.c - removed.changes} 条, 上限 ${limit})`);
                            }
                        }
                    } catch (e) {
                        console.error(`[SQLite Cache] 软上限淘汰(${cat}) error:`, e.message);
                    }
                }
            } catch (e) {
                console.error('[SQLite Cache] Cleanup error:', e.message);
            }
        }
    }
}

const cacheManager = new CacheManager(CACHE_TYPE);
cacheManager.cleanup();   // json 模式:启动时先把上次留在文件里的过期条目清掉

// 定期清理过期缓存 (每小时执行一次)
setInterval(() => {
    cacheManager.cleanup();
}, 60 * 60 * 1000);

// ========== 中间件配置 ==========

// 启用 Gzip/Brotli 压缩
const compression = require('compression');
app.use(compression({
    level: 6,  // 压缩级别 1-9，6 是性能与压缩率的平衡点
    threshold: 1024,  // 只压缩大于 1KB 的响应
    filter: (req, res) => {
        // 不压缩 SSE 事件流
        if (req.headers['accept'] === 'text/event-stream') {
            return false;
        }
        return compression.filter(req, res);
    }
}));

app.use(cors());
app.use(bodyParser.json({ limit: '5mb' }));  // 增大限制以支持历史记录同步

// ========== API 速率限制 ==========
const rateLimit = require('express-rate-limit');
// ipKeyGenerator：把 IP 归一化为限流 key（IPv6 归并到子网前缀，避免同一 /64 轮换绕过限流）
const { ipKeyGenerator } = require('express-rate-limit');
const ipKey = (req) => ipKeyGenerator(getClientIP(req) || req.ip || '0.0.0.0');

// 通用 API 限流：每 IP 每分钟最多 600 次请求
// 注意：页面加载时会发送大量图片和 API 请求，需要足够高的限制
const apiLimiter = rateLimit({
    windowMs: 60 * 1000, // 1 分钟窗口
    max: 600, // 每 IP 最多 600 次（约 10 次/秒）
    standardHeaders: true, // 返回 RateLimit-* 标准头
    legacyHeaders: false, // 禁用 X-RateLimit-* 旧头
    // 用真实客户端 IP 计数（CF-Connecting-IP/X-Real-IP），否则反代后会把所有用户算作同一个 IP
    keyGenerator: ipKey,
    message: { error: '请求过于频繁，请稍后再试 (Rate limit exceeded)' },
    skip: (req) => {
        // 跳过静态资源请求
        if (!req.path.startsWith('/api/')) return true;
        // 配置、认证、站点列表请求不限流（页面加载必需）
        if (req.path === '/api/config' || req.path.startsWith('/api/auth/') || req.path === '/api/sites') return true;
        // 图片代理请求不限流（前端有大量图片）
        if (req.path.startsWith('/api/tmdb-image/')) return true;
        // TMDB 代理请求不限流
        if (req.path === '/api/tmdb-proxy') return true;
        return false;
    }
});

// 搜索 API 更严格的限流：每 IP 每分钟最多 120 次搜索
const searchLimiter = rateLimit({
    windowMs: 60 * 1000,
    max: 120,
    keyGenerator: ipKey,
    message: { error: '搜索请求过于频繁，请稍后再试' }
});

// 应用通用限流
app.use(apiLimiter);

// 对搜索 API 应用更严格的限流
app.use('/api/search', searchLimiter);
// 🎌 Kazumi 规则源的播放端点:/api/kz/ep(解析成 {type,url})、/api/kz/m3u8(同源清单)、/api/kz/mp4(302 签名直链)
if (kazumi) { try { kazumi.registerRoutes(app); } catch (e) { console.warn('[Kazumi] 路由注册失败:', e.message); } }
// ✂️ 剪掉插播后的清单托管(Safari 原生 HLS / AirPlay / 投屏用,见 lib/hls-cut):服务器只存客户端交上来的清单,自己不拉任何 m3u8。
//    POST 不强制登录(内容只是规范化后的公网分片清单,12h 空闲过期;Safari 只拉一次占位清单,续期/重建靠客户端回到前台、emptied 或报错时用同一 id 重新 POST),靠每 IP 限流 + 全站预算防滥用;被封禁的令牌拒绝。
//    HLS_CUT_DISABLE=1 关闭(前端据 /api/config 的 hls_cut 退回"播放中静默跳过")。
const HLS_CUT_ENABLED = !envFlag('HLS_CUT_DISABLE');
let hlsCut = null;
try {
    if (HLS_CUT_ENABLED) {
        const hlsCutLimiter = rateLimit({ windowMs: 60 * 1000, max: 30, keyGenerator: ipKey, message: { error: 'busy' } });
        const own = (token) => typeof token === 'string' && Object.prototype.hasOwnProperty.call(PASSWORD_HASH_MAP, token);
        hlsCut = require('./lib/hls-cut').registerRoutes(app, {
            postLimiter: hlsCutLimiter,
            ipOf: ipKey,
            // 来源 = IP(+ 有效令牌):单密码站所有人共用一个令牌,只按令牌分会把"每来源 12 条"变成全站 12 条
            ownerOf: (req, body) => 'ip:' + ipKey(req) + ((body && own(body.token)) ? '|t:' + body.token : ''),
            authorize: (token) => (token && own(token) && isBanned(token)) ? 'banned' : 'ok'
        });
    }
} catch (e) { console.warn('[HlsCut] 路由注册失败,原生 HLS 播放前去插播已禁用:', e.message); }
// 用户令牌校验:只认 PASSWORD_HASH_MAP 自有属性(原型键 'constructor' 等曾绕过登录)
const ownToken = (token) => typeof token === 'string' && Object.prototype.hasOwnProperty.call(PASSWORD_HASH_MAP, token);
// 后台发通知(收藏更新/求片结果)前的令牌闸门 —— 只管"发不发",接口鉴权仍用 ownToken;封禁在两个模块里另判。
//   · 独立密码/主密码令牌:还在 PASSWORD_HASH_MAP 里才发(站长删了/改了这个密码 → 不再发给旧令牌)
const notifyTokenOk = (token) => ownToken(token);
// 🔔 Web Push(见 lib/webpush):VAPID 密钥优先读 env VAPID_PUBLIC_KEY/VAPID_PRIVATE_KEY,没有就首次启动自动生成存 SQLite(站长无需提供);
//    订阅地址只收已知推送服务主机(防 SSRF);发送失败绝不抛给调用方。需 CACHE_TYPE=sqlite,否则 /api/push/key 报 enabled:false、前端隐藏开关。
let webPush = null;
try {
    webPush = require('./lib/webpush').createWebPush({
        db: () => REQ_DB_OK() ? cacheManager.db : null,
        tokenOk: ownToken,             // 接口鉴权(订阅/退订/测试通知)
        notifyOk: notifyTokenOk,       // 每次发送前现判(见 notifyTokenOk)
        isBanned: (token) => isBanned(token),
    });
    webPush.registerRoutes(app);
} catch (e) { console.warn('[WebPush] 模块加载失败,推送已禁用:', e.message); webPush = null; }
// 求片状态变为 已履行/需补充/已拒绝 → 推送给提交人(单条:POST /api/requests/admin;批量:lib/user-stats 回调)。发完不等,失败只记日志
const REQ_PUSH_BODY = { fulfilled: '有结果了,点开查看', need_info: '站长需要你补充一些信息', rejected: '暂时没能找到,点开查看说明' };
function notifyRequestStatus(list) {
    if (!webPush) return;
    for (const r of (Array.isArray(list) ? list : [list])) {
        if (!r || !r.user_token || r.from === r.to || !Object.prototype.hasOwnProperty.call(REQ_PUSH_BODY, r.to)) continue;
        webPush.sendToUser(r.user_token, {
            title: '《' + String(r.name || '').slice(0, 40) + '》求片有结果了', body: REQ_PUSH_BODY[r.to],
            url: '/?requests=1', tag: 'req:' + r.id
        });
    }
}
// 📊 观看/分享实测统计 + 站长后台查询(见 lib/user-stats):前端按"视频真在走且页面在前台"计秒攒批上报,分享链带 s=<分享码> 追踪回流;
//    站长接口(/api/admin/overview|users|user|shares|requests)全是 SQL 聚合 + 20s 缓存,不再逐行解析 user_history 卡死全站。
//    需 CACHE_TYPE=sqlite;STATS_DISABLE=1 关闭采集(上报接口 204,/api/config.watch_stats=false)。
//    deps 全是调用时才取值的闭包:REQ_DB_OK/adminAuthed 定义在下面,构造时还在 TDZ。
const STATS_ENABLED = !envFlag('STATS_DISABLE');
let userStats = null;
try {
    userStats = require('./lib/user-stats').createUserStats({
        db: () => REQ_DB_OK() ? cacheManager.db : null,
        enabled: () => STATS_ENABLED && !!REQ_DB_OK(),
        // 只认内存表;重启后还没 /check 的机场 token,模块的三个上报接口另按 user_stats 登录记录放行(不影响其它接口鉴权)
        tokenInfo: (token) => (typeof token === 'string' && Object.prototype.hasOwnProperty.call(PASSWORD_HASH_MAP, token)) ? PASSWORD_HASH_MAP[token] : null,
        isBanned: (token) => isBanned(token),
        identity: (token, label) => userIdentity(token, label),
        adminAuthed: (req) => adminAuthed(req),
        ipKey,
        onRequestStatus: (rows) => notifyRequestStatus(rows)   // 后台批量改求片状态 → 推送提交人
    });
    userStats.registerRoutes(app);
} catch (e) { console.warn('[UserStats] 模块加载失败,观看/分享统计与新版站长接口已禁用:', e.message); userStats = null; }
// 🔥 大家都在看(见 lib/popular):watch_stats 近 7 天,除调用者自己以外至少 2 个其他用户(每人 ≥120s)看过才上榜,只给片名(不给人数/时长);
//    10 分钟全站候选缓存(贡献者令牌只在内存),每个请求扣掉调用者再筛。配了访问密码要有效令牌(?token=)。需 sqlite + 统计开启
let popular = null;
try {
    popular = require('./lib/popular').createPopular({
        db: () => REQ_DB_OK() ? cacheManager.db : null,
        enabled: () => STATS_ENABLED && !!REQ_DB_OK(),
        authRequired: () => ACCESS_PASSWORDS.length > 0,
        tokenOk: ownToken,
        isBanned: (token) => isBanned(token)
    });
    popular.registerRoutes(app);
} catch (e) { console.warn('[Popular] 模块加载失败,大家都在看已禁用:', e.message); popular = null; }
// ❤️ 收藏(追剧)+ 更新提醒(见 lib/favorites):每用户 ≤100 部、全站跟踪 ≤3000 个 (站, 片);后台每 10 分钟只调 maccms 详情 API
//    批量查集数(每站每批 ≤20 id、每轮 ≤60 请求、并发 2,绝不拉 m3u8),集数变多 → 推送给收藏了它的用户。
//    需 sqlite;FAV_CHECK_DISABLE=1 只关后台检查(收藏本身照常可用)。匿名 /api/favorites/status 每 IP 30 次/分;
//    配了访问密码时它也要有效令牌(新登记预算按令牌算)。
const FAV_CHECK_ENABLED = !envFlag('FAV_CHECK_DISABLE');
const favSites = () => allSites().filter(s => !(kazumi && kazumi.isKzSite(s)));
let favorites = null;
try {
    favorites = require('./lib/favorites').createFavorites({
        db: () => REQ_DB_OK() ? cacheManager.db : null,
        checkEnabled: () => FAV_CHECK_ENABLED && !process.env.VERCEL,
        authRequired: () => ACCESS_PASSWORDS.length > 0,
        tokenOk: ownToken,
        notifyOk: notifyTokenOk,       // 集数变多时给谁发(见 notifyTokenOk)
        isBanned: (token) => isBanned(token),
        adminAuthed: (req) => adminAuthed(req),
        ipKey,
        // 只有 maccms 站能查更新(番剧规则站 kz_* 是 HTML 刮削,不查)
        sites: favSites,
        // 后台检查用:配了 REMOTE_DB_URL 而远程配置还没加载过 → 先按 /api/sites 的同一套逻辑拉;拉不到 → null(本轮跳过,不碰任何行)
        loadSites: async () => {
            if (REMOTE_DB_URL && !remoteDbCache && !(await loadRemoteDb())) return null;
            return favSites();
        },
        // bg:不做代理对比、不写共享的代理记忆;直连失败走代理要先 ctl.extra() 占本轮请求预算
        fetchJson: async (url, siteKey, timeout, ctl) => (await fetchWithProxyFallback(url, { timeout: timeout || 10000, maxContentLength: 8 * 1024 * 1024, bg: true, extra: ctl && ctl.extra }, siteKey)).data,
        push: (token, payload) => webPush ? webPush.sendToUser(token, payload) : Promise.resolve(null),
        statusLimiter: rateLimit({ windowMs: 60 * 1000, max: 30, keyGenerator: ipKey, message: { error: '请求过于频繁' } })
    });
    favorites.registerRoutes(app);
    favorites.start();   // 启动 60s 后第一轮,之后每 10 分钟(模块内部到下一轮事件循环才判开关,避开 TDZ)
} catch (e) { console.warn('[Favorites] 模块加载失败,收藏与更新提醒已禁用:', e.message); favorites = null; }

// ========== 静态资源配置 ==========

// 静态资源 30天缓存 (libs 目录 - CSS/JS) - 这些文件不会变化
app.use('/libs', express.static('public/libs', {
    maxAge: '30d',
    immutable: true,
    etag: true,
    lastModified: true
}));

// 图片缓存目录 - 30天缓存
app.use('/cache', express.static('public/cache', {
    maxAge: '30d',
    immutable: true,
    etag: true
}));

// ========== 自动识别站点 URL ==========

/**
 * 从请求自动识别当前站点的 URL
 * 优先级：SITE_URL 环境变量 > 请求头自动检测
 * @param {object} req - Express 请求对象
 * @returns {string} - 站点 URL，如 https://mysite.com（不带尾部斜杠）
 */
function getSiteUrl(req) {
    // 1. 优先使用环境变量（用户显式配置的优先级最高）
    if (process.env.SITE_URL) {
        return process.env.SITE_URL.replace(/\/$/, '');
    }
    // 2. 从请求头自动检测
    const protocol = req.headers['x-forwarded-proto'] || req.protocol || 'https';
    const host = req.headers['x-forwarded-host'] || req.get('host');
    if (host) {
        return `${protocol}://${host}`;
    }
    // 3. 兜底默认值
    return 'https://ednovas.video';
}

// 缓存读取的 index.html 原始内容（避免每次请求都读磁盘）
let indexHtmlTemplate = null;
let robotsTxtTemplate = null;

const DEFAULT_SITE_URL = 'https://ednovas.video';

// 🔗 社交平台抓取卡片的爬虫 UA（微信/Twitter/FB/Telegram/Google 等）
function isSocialCrawler(req) {
    const ua = (req.headers['user-agent'] || '').toLowerCase();
    return /bot|crawl|spider|facebookexternalhit|twitterbot|whatsapp|telegram|slackbot|discordbot|linkedinbot|embedly|pinterest|redditbot|googlebot|bingbot|baiduspider|bytespider|sogou|yisou|360spider|micromessenger|qqbrowser|qq\/|weibo|line-poker|skypeuripreview/i.test(ua);
}

// 🔗 分享深链富预览页：按剧名输出 OG/Twitter 卡片，再 JS 跳转回 SPA。
//    只给社交爬虫返回此页；真实用户照常拿 SPA（SPA 自己解析 ?play= 打开剧）。
async function renderSharePage(req, res, rawName) {
    const name = String(rawName || '').slice(0, 100);
    const siteUrl = getSiteUrl(req);
    let poster = `${siteUrl}/icon.png`;
    // 尽力用 TMDB 搜一张海报作为卡片大图（失败/超时则用站点图标，不阻塞）
    try {
        const TMDB_API_KEY = process.env.TMDB_API_KEY;
        if (TMDB_API_KEY && name) {
            const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];
            const serverInChina = process.env['SERVER_IN_CHINA'] === 'true';
            const base = (TMDB_PROXY_URL && serverInChina) ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3` : 'https://api.themoviedb.org/3';
            const r = await axios.get(`${base}/search/multi`, { params: { api_key: TMDB_API_KEY, language: 'zh-CN', query: name }, timeout: 2500 });
            const hit = ((r.data && r.data.results) || []).find(x => x.poster_path || x.backdrop_path);
            if (hit) poster = `https://image.tmdb.org/t/p/w500${hit.poster_path || hit.backdrop_path}`;
        }
    } catch (e) { /* 忽略，用站点图标 */ }

    const eName = escapeHtml(name);
    const ePoster = escapeHtml(poster);
    const desc = escapeHtml(`在 E视界 免费在线观看《${name}》，多线路高清播放。`);
    const playUrl = `${siteUrl}/?play=${encodeURIComponent(name)}`;
    // 📊 分享码 s 要跟着跳回 SPA:微信/QQ 内置浏览器的真人也会先落到这一页(isSocialCrawler 把它们算进来了),丢了就记不到"带来登录"
    const shareCode = /^[A-Za-z0-9]{6,16}$/.test(String(req.query.s || '')) ? String(req.query.s) : '';
    const spaUrl = `/?play=${encodeURIComponent(name)}&_spa=1${shareCode ? '&s=' + shareCode : ''}`;
    const html = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>${eName} - 在线观看 | E视界</title>
<meta name="description" content="${desc}">
<link rel="canonical" href="${escapeHtml(playUrl)}">
<meta property="og:type" content="video.other">
<meta property="og:title" content="${eName} - 在线观看">
<meta property="og:description" content="${desc}">
<meta property="og:image" content="${ePoster}">
<meta property="og:url" content="${escapeHtml(playUrl)}">
<meta property="og:site_name" content="E视界">
<meta name="twitter:card" content="summary_large_image">
<meta name="twitter:title" content="${eName} - 在线观看">
<meta name="twitter:description" content="${desc}">
<meta name="twitter:image" content="${ePoster}">
<meta http-equiv="refresh" content="0;url=${escapeHtml(spaUrl)}">
<script>location.replace(${JSON.stringify(spaUrl)});</script>
</head>
<body style="background:#141414;color:#fff;font-family:-apple-system,sans-serif;text-align:center;padding:40px;">
<h1>${eName}</h1>
<p>正在进入播放页…若未自动跳转，请 <a href="${escapeHtml(spaUrl)}" style="color:#e50914;">点此进入</a></p>
</body>
</html>`;
    res.set('Cache-Control', 'public, max-age=600');
    res.type('html').send(html);
}

// ⚠️ 关键：动态注入站点 URL 到 index.html
// 自动将 meta 标签中的 ednovas.video 替换为当前访问的网站地址
app.get(['/', '/index.html'], async (req, res) => {
    // 📊 分享回流:?s=<分享码> → 记一次打开(真人)/预览(平台抓卡片)。放在分支之前 = 爬虫页与 SPA 两条路都覆盖;
    //    同步的几次索引小查询,异常在模块里吞掉,这里再包一层,绝不影响页面返回。
    //    打开/预览由模块按 UA 自己判:isSocialCrawler 连微信/QQ/搜狗的真人浏览器都算(为了出卡片页),不能拿来区分。
    if (req.query.s && userStats) { try { userStats.recordShareOpen(req); } catch (e) { } }
    // 🔗 分享深链：社交爬虫请求 /?play=剧名 时返回富预览卡片；真实用户(无 bot UA 或带 _spa)照常拿 SPA
    if (req.query.play && !req.query._spa && isSocialCrawler(req)) {
        try { return await renderSharePage(req, res, req.query.play); }
        catch (e) { console.error('[SharePage] error:', e.message); /* 失败则继续返回 SPA */ }
    }
    res.set('Cache-Control', 'no-cache, no-store, must-revalidate');
    res.set('Pragma', 'no-cache');
    res.set('Expires', '0');

    try {
        // 懒加载模板
        if (!indexHtmlTemplate) {
            indexHtmlTemplate = fs.readFileSync(path.join(__dirname, 'public/index.html'), 'utf-8');
        }

        const siteUrl = getSiteUrl(req);

        // 如果当前就是默认地址，不需要替换
        if (siteUrl === DEFAULT_SITE_URL) {
            res.type('html').send(indexHtmlTemplate);
            return;
        }

        // 替换所有 hardcoded 的默认 URL
        const html = indexHtmlTemplate.replace(
            new RegExp(DEFAULT_SITE_URL.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g'),
            siteUrl
        );
        res.type('html').send(html);
    } catch (err) {
        console.error('[Dynamic HTML] Error:', err.message);
        // 回退到静态文件
        res.sendFile(path.join(__dirname, 'public/index.html'));
    }
});

// 动态注入站点 URL 到 robots.txt
app.get('/robots.txt', (req, res) => {
    try {
        if (!robotsTxtTemplate) {
            robotsTxtTemplate = fs.readFileSync(path.join(__dirname, 'public/robots.txt'), 'utf-8');
        }

        const siteUrl = getSiteUrl(req);

        if (siteUrl === DEFAULT_SITE_URL) {
            res.type('text').send(robotsTxtTemplate);
            return;
        }

        const txt = robotsTxtTemplate.replace(
            new RegExp(DEFAULT_SITE_URL.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g'),
            siteUrl
        );
        res.type('text').send(txt);
    } catch (err) {
        console.error('[Dynamic robots.txt] Error:', err.message);
        res.sendFile(path.join(__dirname, 'public/robots.txt'));
    }
});

// Service Worker 不缓存
app.get('/sw.js', (req, res, next) => {
    res.set('Cache-Control', 'no-cache, no-store, must-revalidate');
    res.set('Pragma', 'no-cache');
    res.set('Expires', '0');
    next();
});

// 其他静态文件 - 1小时缓存
app.use(express.static('public', {
    maxAge: '1h',
    etag: true,
    lastModified: true
}));

// ========== 路由定义 ==========

const IS_VERCEL = !!process.env.VERCEL;


// ========== 📺 直播(IPTV)频道：拉取上游 M3U → 解析 → 精选 → 缓存(6h) ==========
// 服务器只负责"拉取+精选+缓存+定时更新"；真正的"测速/线路选择/可用性"放在客户端做——
// 直播多为 http:// 运营商源(混合内容)，实际播放走 CF Worker 代理，客户端在自己网络上测才准。
const LIVE_CACHE_TTL = 6 * 60 * 60 * 1000;
let _liveCache = { at: 0, data: [], ok: false };
let _liveInflight = null;

// 分类映射 + 展示顺序。用户选"全列出不验证"：上游全部频道按分类下发，主页行显示前几类，
// 播放页"快速换台"出 grid + 分类筛选。客户端测线路挑能播的(运营商 IP 源封 CF，放不了)。
const LIVE_GROUP_MAP = {
    '央视频道': '央视', '卫视频道': '卫视', '体育频道': '体育', '电影频道': '影视',
    '纪录频道': '纪实', '儿童频道': '少儿', '音乐频道': '音乐', '春晚频道': '专题',
    '地方频道': '地方', '直播中国': '地方', '数字频道': '数字', '解说频道': '体育'
};
const LIVE_GROUP_ORDER = ['央视', '卫视', '体育', '影视', '电影', '电视剧', '综艺', '新闻', '纪实', '少儿', '音乐', '文化', '教育', '科教', '财经', '生活', '宗教', '购物', '专题', '数字', '地方', '成人', '其他'];
// 主页一行显示的分类(其余靠播放页 grid + 分类浏览)
const LIVE_HOME_GROUPS = new Set(['央视', '卫视', '体育']);

// 🌍 国际频道：iptv-org 按语言的播放列表(每种封顶，控制总量/内存)。lang 从播放列表来，genre 从 group-title。
const LIVE_LANGS = [
    { code: 'eng', name: 'English', cap: 150 }, { code: 'spa', name: 'Español', cap: 150 },
    { code: 'fra', name: 'Français', cap: 150 }, { code: 'deu', name: 'Deutsch', cap: 120 },
    { code: 'rus', name: 'Русский', cap: 120 }, { code: 'ara', name: 'العربية', cap: 120 },
    { code: 'por', name: 'Português', cap: 120 }, { code: 'ita', name: 'Italiano', cap: 100 },
    { code: 'jpn', name: '日本語', cap: 80 }, { code: 'kor', name: '한국어', cap: 80 },
    { code: 'hin', name: 'हिन्दी', cap: 80 }, { code: 'vie', name: 'Tiếng Việt', cap: 80 }
];
const LIVE_LANG_URL = (code) => `https://iptv-org.github.io/iptv/languages/${code}.m3u`;
// 🔞 成人直播源(可选)：由站长用 LIVE_M3U_ADULT(逗号分隔)注入；归入"成人"分类，受前端 NSFW 过滤开关控制显隐。
const LIVE_M3U_ADULT = (process.env['LIVE_M3U_ADULT'] || '').split(',').map(s => s.trim()).filter(Boolean);

// iptv-org group-title(英文 genre) → 中文分类
const LIVE_INTL_GENRE = {
    general: '综艺', news: '新闻', movies: '电影', movie: '电影', series: '电视剧', drama: '电视剧',
    music: '音乐', entertainment: '综艺', sports: '体育', sport: '体育', kids: '少儿', animation: '少儿',
    documentary: '纪实', culture: '文化', education: '教育', science: '科教', business: '财经',
    religious: '宗教', shop: '购物', lifestyle: '生活', cooking: '生活', travel: '生活', comedy: '综艺',
    classic: '电影', family: '综艺', outdoor: '生活', auto: '生活', relax: '生活', weather: '其他', legislative: '新闻'
};
function liveIntlGenre(groupTitle) {
    const g = String(groupTitle || '').toLowerCase().split(';')[0].trim();
    return LIVE_INTL_GENRE[g] || '其他';
}

// 名称归一(合并/去重 key)：去掉清晰度/HD/台/频道等噪声、空格横杠，大写
function liveNormName(name) {
    return String(name || '')
        .replace(/\((?:\d{3,4}[pi]|[^)]*?)\)/gi, '')   // (1080p)/(720p)/(...)
        .replace(/\[[^\]]*\]/g, '')                     // [Not 24/7]
        .replace(/(高清|超清|蓝光|频道|台|HD|FHD|UHD|4K|8K|IPV6|IPV4)/gi, '')
        .replace(/[\s\-_·｜|]/g, '')
        .toUpperCase();
}
// 展示名清理(去清晰度/方括号噪声，保留中文台名)
function liveCleanName(name) {
    return String(name || '').replace(/\s*\((?:\d{3,4}[pi])\)\s*/gi, ' ').replace(/\s*\[[^\]]*\]\s*/g, ' ').replace(/\s+/g, ' ').trim();
}
function liveHostIsIP(u) { try { return /^\d{1,3}(\.\d{1,3}){3}$/.test(new URL(u).hostname); } catch (e) { return true; } }
// 线路可达性打分(越小越靠前)。关键：CF Worker 的 fetch() 只允许标准端口(80/443/8080…)，
// 运营商源多在 :9901/:82 等非标端口 → worker 取不到(403)；裸 IP 也常被封。域名+标准端口才能过。
const LIVE_STD_PORTS = new Set([80, 443, 8080, 8443, 2052, 2053, 2082, 2083, 2086, 2087, 2095, 2096, 8880]);
function liveSrcRank(u) {
    try {
        const url = new URL(u);
        const ip = /^\d{1,3}(\.\d{1,3}){3}$/.test(url.hostname);
        const https = url.protocol === 'https:';
        const port = url.port ? parseInt(url.port, 10) : (https ? 443 : 80);
        const stdPort = LIVE_STD_PORTS.has(port);
        // 智能路由后的可达性：
        //   ① 域名 https → rank 0：客户端【直连】(原生 HLS 免 CORS；hls.js 若带 CORS)，不经 worker，端口/CF 限制都绕开。
        //   ② 域名 http + 标准端口 → rank 1：http 在 https 页是混合内容，必须经 worker 升 https；worker 又只接标准端口。
        //   ③ 裸 IP / 非标端口 http → rank 10+：worker 取不到 + 直连又是混合内容 → 基本放不了。
        if (!ip && https) return 0;
        if (!ip && stdPort) return 1;
        return 10 + (ip ? 2 : 0) + (stdPort ? 0 : 4) + (https ? 0 : 1);
    } catch (e) { return 99; }
}
// 分类判定：先看名字(跨两个上游更稳)，再回退 group-title 映射
function liveCategoryOf(name, groupTitle) {
    const n = String(name || '');
    if (/CCTV|央视|CGTN/i.test(n)) return /(CCTV-?5($|[^0-9])|5\s*[＋+]|体育|赛事|高尔夫|网球|台球|风云足球|斯诺克)/.test(n) ? '体育' : '央视';
    if (/卫视/.test(n)) return '卫视';
    if (/(体育|赛事|足球|篮球|网球|高尔夫|台球|斯诺克|搏击|NBA|ESPN)/i.test(n)) return '体育';
    if (/(电影|影院|剧场|影视|院线)/.test(n)) return '影视';
    if (/(少儿|动画|卡通|动漫|儿童|宝贝|金鹰卡通|嘉佳)/.test(n)) return '少儿';
    if (/(纪录|纪实|探索|科教|地理|discovery)/i.test(n)) return '纪实';
    if (/(新闻|资讯|凤凰)/.test(n)) return '新闻';
    if (/(音乐|MTV|演唱)/i.test(n)) return '音乐';
    return LIVE_GROUP_MAP[groupTitle] || '其他';
}

function parseM3U(text) {
    const out = [];
    const lines = String(text).split(/\r?\n/);
    let cur = null;
    for (const raw of lines) {
        const line = raw.trim();
        if (!line) continue;
        if (line.startsWith('#EXTINF')) {
            const name = line.includes(',') ? line.slice(line.lastIndexOf(',') + 1).trim() : '';
            const logo = (line.match(/tvg-logo="([^"]*)"/i) || [])[1] || '';
            const group = (line.match(/group-title="([^"]*)"/i) || [])[1] || '';
            const tvgId = (line.match(/tvg-id="([^"]*)"/i) || [])[1] || '';
            cur = { name, logo, group, tvgId };
        } else if (line[0] !== '#') {
            if (cur) { cur.url = line; out.push(cur); cur = null; }
        }
    }
    return out;
}

// 合并多路上游 → 按归一名去重 → 分类(语言+种类) → 线路域名优先排序。返回 { channels, groups, langs }。
// 每条上游频道可带 lang(语言显示名)/intl(国际,用 group-title 映射种类)/adult(成人) 标记。
function buildLiveChannels(lists) {
    const map = new Map();   // 归一名 → bucket
    for (const list of lists) {
        for (const c of (list || [])) {
            const u = (c.url || '').trim();
            if (!/^https?:\/\//i.test(u)) continue;   // 浏览器只能播 http(s) m3u8
            const key = liveNormName(c.name);
            if (!key) continue;
            if (/支持作者|更新时间|请刷新|公众号|演示频道|测试频道|^熊猫直播$/.test(c.name)) continue;   // 过滤上游推广/占位条目
            let b = map.get(key);
            if (!b) {
                const adult = !!c.adult;
                const group = adult ? '成人' : (c.intl ? liveIntlGenre(c.group) : liveCategoryOf(c.name, c.group));
                b = { name: liveCleanName(c.name) || c.name, group, lang: c.lang || '中文', adult, logo: '', seen: new Set(), sources: [] };
                map.set(key, b);
            } else {
                const cn = liveCleanName(c.name);
                if (cn && cn.length < b.name.length) b.name = cn;   // 取更短更干净的展示名
            }
            // 台标只收 https(挡混合内容 + 恶意上游 data:/追踪像素)
            if (!b.logo && c.logo && /^https:\/\//i.test(c.logo)) b.logo = c.logo;
            if (!b.seen.has(u) && b.sources.length < 12) {
                b.seen.add(u);
                b.sources.push({ url: u, rank: liveSrcRank(u) });
            }
        }
    }
    const channels = [];
    for (const [key, b] of map) {
        // 线路排序：可达性打分(域名+标准端口 worker 才取得到；运营商非标端口/裸 IP 排最后)
        b.sources.sort((a, z) => a.rank - z.rank);
        channels.push({
            // 保留 '+' —— 否则 "CCTV+1"(归一名 CCTV+1)和 "CCTV1" 去掉加号都成 lv_CCTV1、id 撞车 → 多个频道同时高亮
            id: 'lv_' + key.replace(/[^a-zA-Z0-9一-龥+]/g, '').slice(0, 40),
            name: b.name, group: b.group, lang: b.lang, adult: b.adult, logo: b.logo,
            rank: b.sources.length ? b.sources[0].rank : 99,   // 最优线路可达性(前端把可能能播的排前面)
            sources: b.sources.slice(0, 8).map(s => ({ url: s.url }))
        });
    }
    const langOrder = ['中文', ...LIVE_LANGS.map(l => l.name)];
    const li = (l) => { const i = langOrder.indexOf(l); return i < 0 ? 999 : i; };
    const gi = (g) => { const i = LIVE_GROUP_ORDER.indexOf(g); return i < 0 ? 999 : i; };
    channels.sort((a, z) => li(a.lang) - li(z.lang) || gi(a.group) - gi(z.group) || a.name.localeCompare(z.name, 'zh'));
    const groups = LIVE_GROUP_ORDER.filter(g => channels.some(c => c.group === g));
    const langs = langOrder.filter(l => channels.some(c => c.lang === l));
    return { channels, groups, langs };
}

// 实测一条线路能否播：http 走 worker(=客户端播放路径)、https 直连(≈客户端直连)。拿到 #EXTM3U 即活。
async function probeLiveSource(url) {
    const https = /^https:\/\//i.test(url);
    const target = https ? url : (CORS_PROXY_URL ? `${CORS_PROXY_URL}/?url=${encodeURIComponent(url)}` : null);
    if (!target) return false;   // http 源无 worker 没法验证(也没法播)
    try {
        const r = await axios.get(target, { timeout: 8000, maxContentLength: 8000, responseType: 'text', validateStatus: () => true, headers: { 'User-Agent': 'Mozilla/5.0', 'Range': 'bytes=0-5000' } });
        if (!(r.status === 200 || r.status === 206)) return false;
        const body = String(r.data || '');
        if (!body.includes('#EXTM3U')) return false;
        // 待机/占位/死台不算"能播"(如 catvod 的 backup.m3u8、无信号轮播)——它们返回 200+m3u8 但放不出实际频道
        if (/backup\.m3u8|backup_\d|无\s*信\s*号|no[\s_-]?signal|maintain|stand.?by|占位|轮播图/i.test(body)) return false;
        return true;
    } catch (e) { return false; }
}

// 后台验证：标 ch.ok(首条线路能否播)，能播的在组内排前。不删频道。原地 mutate channels。
async function validateLiveChannels(channels) {
    let i = 0;
    const CONC = 32;
    await Promise.all(Array.from({ length: CONC }, async () => {
        while (i < channels.length) {
            const ch = channels[i++];
            let ok = false;
            for (const s of (ch.sources || []).slice(0, 2)) { if (await probeLiveSource(s.url)) { ok = true; break; } }
            ch.ok = ok;
        }
    }));
    const langOrder = ['中文', ...LIVE_LANGS.map(l => l.name)];
    const li = (l) => { const x = langOrder.indexOf(l); return x < 0 ? 999 : x; };
    const gi = (g) => { const x = LIVE_GROUP_ORDER.indexOf(g); return x < 0 ? 999 : x; };
    // 语言 → 分类 → 能播优先 → rank → 名称
    channels.sort((a, z) => li(a.lang) - li(z.lang) || gi(a.group) - gi(z.group) || ((z.ok ? 1 : 0) - (a.ok ? 1 : 0)) || (a.rank - z.rank) || a.name.localeCompare(z.name, 'zh'));
    return channels;
}

async function fetchLiveUpstream() {
    const get = async (urls) => {
        for (const u of urls) {
            try {
                const r = await axios.get(u, { timeout: 12000, responseType: 'text', headers: { 'User-Agent': 'Mozilla/5.0' } });
                if (r.data && String(r.data).includes('#EXTINF')) return String(r.data);
            } catch (e) { /* 试下一个 */ }
        }
        return '';
    };
    // LIVE_M3U_DISABLE=1 时只拉 LIVE_M3U_EXTRA，关掉所有内置上游(vbskycn/iptv-org/国际/内置CCTV5源)
    const [vbText, orgText, zhoText, ...extraTexts] = await Promise.all([
        LIVE_BUILTIN ? get([LIVE_M3U_URL, LIVE_M3U_FALLBACK].filter(Boolean)) : Promise.resolve(''),
        LIVE_BUILTIN ? get([LIVE_M3U_IPTVORG].filter(Boolean)) : Promise.resolve(''),
        LIVE_BUILTIN ? get([LIVE_M3U_ZHO].filter(Boolean)) : Promise.resolve(''),
        ...LIVE_M3U_EXTRA.map(u => get([u]))
    ]);
    if (!vbText && !orgText && !zhoText && !extraTexts.some(Boolean) && LIVE_BUILTIN) throw new Error('upstream M3U fetch failed');
    const vbList = parseM3U(vbText), orgList = parseM3U(orgText), zhoList = parseM3U(zhoText);   // 中文(lang 默认中文)；zho 含海外 CDN 华语源
    const extraLists = extraTexts.map(t => parseM3U(t));           // 用户自定义付费源(LIVE_M3U_EXTRA)优先
    // 🌍 国际：按语言拉 iptv-org，每种封顶；intl 标记 → 用 group-title 映射种类
    const langLists = LIVE_BUILTIN ? await Promise.all(LIVE_LANGS.map(async lg => {
        const t = await get([LIVE_LANG_URL(lg.code)]);
        return parseM3U(t).slice(0, lg.cap).map(c => ({ ...c, lang: lg.name, intl: true }));
    })) : [];
    // 🔞 成人(站长用 LIVE_M3U_ADULT 注入)：归入"成人"分类，受前端 NSFW 过滤控制
    const adultTexts = await Promise.all(LIVE_M3U_ADULT.map(u => get([u])));
    const adultList = adultTexts.flatMap(t => parseM3U(t).map(c => ({ ...c, adult: true })));
    // 内置免费 CCTV5/5+ 放在最前：与上游同名归并时其 https 线路被优先播(LIVE_M3U_DISABLE 时一并关掉)
    const kafeiList = LIVE_BUILTIN ? LIVE_KAFEI_GEN : [];
    const built = buildLiveChannels([kafeiList, ...extraLists, vbList, orgList, zhoList, ...langLists, adultList]);
    const intlN = langLists.reduce((s, l) => s + l.length, 0);
    console.log(`[直播] 上游拉取：中文 ${vbList.length + orgList.length}${zhoList.length ? '+zho' + zhoList.length : ''}${kafeiList.length ? '+kafei' + kafeiList.length : ''}${LIVE_M3U_EXTRA.length ? '+extra' + extraLists.reduce((s, l) => s + l.length, 0) : ''} + 国际 ${intlN}(${LIVE_LANGS.length}语) + 成人 ${adultList.length} → 合并 ${built.channels.length} 频道 / ${built.groups.length} 类 / ${built.langs.length} 语`);
    // 后台验证(不阻塞返回)：完成后原地标 ok + 重排，并刷新缓存时间戳让客户端 SWR 取到新版
    if (LIVE_VALIDATE && CORS_PROXY_URL) {
        validateLiveChannels(built.channels).then(() => {
            _liveCache.at = Date.now();
            console.log(`[直播] 验证完成：${built.channels.filter(c => c.ok).length}/${built.channels.length} 可播`);
        }).catch(e => console.error('[直播] 验证失败:', e.message));
    }
    return built;
}

// 取直播频道(带 6h 缓存 + 并发合并 + 旧缓存兜底)
async function getLiveChannels(force = false) {
    if (!force && _liveCache.ok && (Date.now() - _liveCache.at) < LIVE_CACHE_TTL) return _liveCache.data;
    if (_liveInflight) return _liveInflight;
    _liveInflight = (async () => {
        try {
            const data = await fetchLiveUpstream();
            _liveCache = { at: Date.now(), data, ok: true };
            return data;
        } catch (e) {
            console.error('[直播] 刷新失败:', e.message);
            if (_liveCache.ok) return _liveCache.data;   // 拉取失败时沿用旧缓存
            _liveCache = { at: Date.now(), data: { channels: [], groups: [], langs: [] }, ok: false };
            return _liveCache.data;
        } finally { _liveInflight = null; }
    })();
    return _liveInflight;
}

// 📺 直播频道列表(精选 + 6h 缓存)。前端再本地缓存。
app.get('/api/live/channels', async (req, res) => {
    if (!LIVE_TV_ENABLED) return res.json({ enabled: false, channels: [], groups: [], langs: [] });
    try {
        const data = await getLiveChannels(false);
        res.set('Cache-Control', 'public, max-age=1800');   // 客户端/CDN 缓存 30 分钟
        res.json({ enabled: true, updatedAt: _liveCache.at, count: data.channels.length, channels: data.channels, groups: data.groups, langs: data.langs });
    } catch (e) {
        res.json({ enabled: true, channels: [], groups: [], langs: [], error: 'fetch_failed' });
    }
});

// 启动后预热缓存(非阻塞)，让首位用户也能秒开直播区
if (LIVE_TV_ENABLED && !IS_VERCEL) { getLiveChannels(false).catch(() => {}); }


app.get('/api/config', (req, res) => {
    // 检查请求中的 token 是否支持同步
    const userToken = req.query.token || '';
    const userInfo = PASSWORD_HASH_MAP[userToken];
    const syncEnabled = userInfo ? userInfo.syncEnabled : false;

    res.json({
        tmdb_api_key: process.env.TMDB_API_KEY,
        tmdb_proxy_url: process.env['TMDB_PROXY_URL'],
        // CORS 代理 URL（用于中转无法直接访问的资源站 API）。cors_proxy_url=主代理(向后兼容);
        // cors_proxy_urls=全部代理(前端故障时轮换到备用 worker)
        cors_proxy_url: CORS_PROXY_URL || null,
        cors_proxy_urls: CORS_PROXY_URLS,
        // Vercel 环境下禁用本地图片缓存，防止写入报错
        enable_local_image_cache: !IS_VERCEL,
        // 多用户同步功能
        sync_enabled: syncEnabled,
        multi_user_mode: ACCESS_PASSWORDS.length > 1,
        // 🗨️ 弹幕：配置了 DANMU_API_URL 才开启(前端据此决定是否给播放器挂弹幕)
        danmaku_enabled: !!process.env.DANMU_API_URL,
        // 📮 求片：必须配置 ADMIN_TOKEN(站长才能履行)才开启;否则前端整个隐藏入口、后端拒收
        requests_enabled: !!process.env.ADMIN_TOKEN,
        // 📺 直播(IPTV)：默认开启，设 LIVE_TV_DISABLED=1 关闭 → 前端隐藏直播区
        live_enabled: LIVE_TV_ENABLED,
        // ✂️ 剪掉插播后的清单托管可用(Safari 原生 HLS 播放前去插播要它;Vercel 无状态 → false)
        hls_cut: !!hlsCut,
        // 📊 观看计时/分享追踪上报开关(需 sqlite;STATS_DISABLE=1 关)
        watch_stats: !!(userStats && userStats.enabled()),
        // 🔔 推送可用(需 sqlite + web-push 依赖;密钥自动生成)/ ❤️ 服务器收藏可用(需 sqlite;没开就只用本机收藏)
        push_enabled: !!(webPush && webPush.enabled()),
        favorites_enabled: !!(favorites && favorites.enabled()),
        // 🚫 封禁：站长在后台封了这个用户 → 前端锁屏
        banned: isBanned(userToken)
    });
});

// 健康检查端点（不泄露环境配置：原先会暴露密码数量、各 env 是否配置，便于攻击者侦察）
app.get('/api/debug', (req, res) => {
    res.json({
        status: 'ok',
        timestamp: new Date().toISOString()
    });
});

// ========== 历史记录同步 API ==========
// 📦 历史条目瘦身(只留上次线路的选集串、去掉简介与本机测速字段),与前端推送前的规则一致(lib/history-slim)
const { slimHistoryItem } = require('./lib/history-slim');

// 获取服务器上的历史记录
app.get('/api/history/pull', (req, res) => {
    const userToken = req.query.token;

    if (!userToken) {
        return res.status(400).json({ error: 'Missing token' });
    }

    // 验证 token 是否有效且启用同步
    const userInfo = PASSWORD_HASH_MAP[userToken];
    if (!userInfo) {
        return res.status(401).json({ error: 'Invalid token' });
    }
    if (!userInfo.syncEnabled) {
        return res.json({ sync_enabled: false, history: [] });
    }

    // 从 SQLite 获取历史记录
    if (cacheManager.type !== 'sqlite' || !cacheManager.db) {
        return res.json({ sync_enabled: true, history: [], message: 'SQLite not available' });
    }

    try {
        // 只下发最近 100 部(客户端本地只留 50):旧版每次启动整份下发,历史只增不减时越来越大
        const stmt = cacheManager.db.prepare('SELECT item_id, item_data, updated_at FROM user_history WHERE user_token = ? ORDER BY updated_at DESC LIMIT 100');
        const rows = stmt.all(userToken);

        // 旧客户端存进来的胖条目(每条线路的完整选集串、简介、测速字段)下发时瘦身,并顺手写回(一次性迁移,之后就小了)
        const rewrite = cacheManager.db.prepare('UPDATE user_history SET item_data = ? WHERE user_token = ? AND item_id = ? AND updated_at = ?');
        const history = rows.map(row => {
            let data = JSON.parse(row.item_data);
            if (row.item_data.length > 20000) {
                data = slimHistoryItem(data);
                try { rewrite.run(JSON.stringify(data), userToken, row.item_id, row.updated_at); } catch (e) { }
            }
            return { id: row.item_id, data, updated_at: row.updated_at };
        });

        res.json({ sync_enabled: true, history: history });
    } catch (e) {
        console.error('[History Pull Error]', e.message);
        res.status(500).json({ error: 'Database error' });
    }
});

// 推送历史记录到服务器
app.post('/api/history/push', (req, res) => {
    const { token, history } = req.body;

    if (!token || !Array.isArray(history)) {
        return res.status(400).json({ error: 'Missing token or history' });
    }

    // 验证 token
    const userInfo = PASSWORD_HASH_MAP[token];
    if (!userInfo) {
        return res.status(401).json({ error: 'Invalid token' });
    }
    if (!userInfo.syncEnabled) {
        return res.json({ sync_enabled: false, saved: 0 });
    }

    // 保存到 SQLite
    if (cacheManager.type !== 'sqlite' || !cacheManager.db) {
        return res.json({ sync_enabled: true, saved: 0, message: 'SQLite not available' });
    }

    try {
        const insertStmt = cacheManager.db.prepare(`
            INSERT OR REPLACE INTO user_history (user_token, item_id, item_data, updated_at)
            VALUES (?, ?, ?, ?)
        `);

        // 获取当前服务器上该用户的所有记录 ID
        const existingIds = cacheManager.db.prepare(
            'SELECT item_id FROM user_history WHERE user_token = ?'
        ).all(token).map(row => row.item_id);

        // 计算需要删除的 ID（服务器有但本地没有的）
        const pushingIds = new Set(history.map(item => item.id));
        const idsToDelete = existingIds.filter(id => !pushingIds.has(id));

        let saved = 0;
        const transaction = cacheManager.db.transaction(() => {
            // 1. 插入历史，但被【更新的删除墓碑】压制的不入库(防复活)；若该条比墓碑更新=重新观看,清墓碑后入库
            // 增量推送后一次只有几条;老客户端全量推送也最多收 200 条
            for (const item of history.slice(0, 200)) {
                if (!item.id || !item.data) continue;
                const upd = item.updated_at || Date.now();
                const td = tomb.get(item.id);
                if (td != null && td >= upd) { deleteHist.run(token, item.id); continue; }  // 删除比这次观看新 → 压制
                if (td != null) tomb.delete(item.id);  // 这次观看更新 → 重新观看,墓碑作废
                // ⏱️ 更新者胜(last-writer-wins)：服务器已有更新的版本(别的设备看到了更靠后的集/进度) → 不被旧推送覆盖。
                //    根治"iPad 看到16集、手机却把进度压回14集"——陈旧设备的旧 updated_at 推送不再 INSERT OR REPLACE 掉新数据。
                const cur = existingUpd.get(item.id);
                // 时间戳相同 = 同一个版本(旧版全量推送每分钟都会把所有行重写一遍),跳过
                if (cur != null && cur >= upd) continue;
                // 入库前瘦身(老客户端推的胖条目也一样);瘦身后仍超 64KB 的异常条目不收
                const json = JSON.stringify(slimHistoryItem(item.data));
                if (json.length > 65536) continue;
                insertStmt.run(token, item.id, json, upd);
                saved++;
            }

            // 2. 删除本地已删除的记录
            if (idsToDelete.length > 0) {
                const deleteStmt = cacheManager.db.prepare(
                    'DELETE FROM user_history WHERE user_token = ? AND item_id = ?'
                );
                for (const id of idsToDelete) {
                    deleteStmt.run(token, id);
                    deleted++;
                }
                console.log(`[History Sync] 删除了 ${deleted} 条已移除的记录:`, idsToDelete);
            }
        });

        transaction(history);

        res.json({ sync_enabled: true, saved: saved, deleted: deleted });
    } catch (e) {
        console.error('[History Push Error]', e.message);
        res.status(500).json({ error: 'Database error' });
    }
});

// 清除用户历史记录 (服务器端)
app.post('/api/history/clear', (req, res) => {
    const { token } = req.body;

    if (!token) {
        return res.status(400).json({ error: 'Missing token' });
    }

    // 验证 token
    const userInfo = PASSWORD_HASH_MAP[token];
    if (!userInfo) {
        return res.status(401).json({ error: 'Invalid token' });
    }

    // 从 SQLite 删除该用户的所有历史
    if (cacheManager.type !== 'sqlite' || !cacheManager.db) {
        return res.json({ success: true, message: 'SQLite not available' });
    }

    try {
        const deleteStmt = cacheManager.db.prepare(`
            DELETE FROM user_history WHERE user_token = ?
        `);
        const result = deleteStmt.run(token);
        console.log(`[History Clear] 用户 ${token.substring(0, 8)}... 删除了 ${result.changes} 条记录`);
        res.json({ success: true, deleted: result.changes });
    } catch (e) {
        console.error('[History Clear Error]', e.message);
        res.status(500).json({ error: 'Database error' });
    }
});

// ========== 用户设置同步 API（跨设备记住偏好，如弹幕开关）==========

// 拉取用户设置
app.get('/api/settings/pull', (req, res) => {
    const userToken = req.query.token;
    if (!userToken) return res.status(400).json({ error: 'Missing token' });
    const userInfo = PASSWORD_HASH_MAP[userToken];
    if (!userInfo) return res.status(401).json({ error: 'Invalid token' });
    if (isBanned(userToken)) return res.status(403).json({ error: 'banned', banned: true });
    if (!userInfo.syncEnabled) return res.json({ sync_enabled: false, settings: {} });
    if (cacheManager.type !== 'sqlite' || !cacheManager.db) {
        return res.json({ sync_enabled: true, settings: {}, message: 'SQLite not available' });
    }
    try {
        const row = cacheManager.db.prepare('SELECT settings_data FROM user_settings WHERE user_token = ?').get(userToken);
        let settings = {};
        if (row && row.settings_data) { try { settings = JSON.parse(row.settings_data) || {}; } catch (e) { } }
        res.json({ sync_enabled: true, settings });
    } catch (e) {
        console.error('[Settings Pull Error]', e.message);
        res.status(500).json({ error: 'Database error' });
    }
});

// 推送用户设置（整体合并保存；前端只传变化的键也可，这里做浅合并）
app.post('/api/settings/push', (req, res) => {
    const { token, settings } = req.body;
    if (!token || typeof settings !== 'object' || settings === null) {
        return res.status(400).json({ error: 'Missing token or settings' });
    }
    const userInfo = PASSWORD_HASH_MAP[token];
    if (!userInfo) return res.status(401).json({ error: 'Invalid token' });
    if (isBanned(token)) return res.status(403).json({ error: 'banned', banned: true });
    if (!userInfo.syncEnabled) return res.json({ sync_enabled: false, saved: 0 });
    if (cacheManager.type !== 'sqlite' || !cacheManager.db) {
        return res.json({ sync_enabled: true, saved: 0, message: 'SQLite not available' });
    }
    try {
        // 浅合并已存在的设置，避免一次只传一个键时把其它键覆盖丢失
        const existing = cacheManager.db.prepare('SELECT settings_data FROM user_settings WHERE user_token = ?').get(token);
        let merged = {};
        if (existing && existing.settings_data) { try { merged = JSON.parse(existing.settings_data) || {}; } catch (e) { } }
        merged = { ...merged, ...settings };
        cacheManager.db.prepare(`
            INSERT OR REPLACE INTO user_settings (user_token, settings_data, updated_at) VALUES (?, ?, ?)
        `).run(token, JSON.stringify(merged), Date.now());
        res.json({ sync_enabled: true, saved: 1, settings: merged });
    } catch (e) {
        console.error('[Settings Push Error]', e.message);
        res.status(500).json({ error: 'Database error' });
    }
});

// ========== ⏭️ 跳过片头 API：共享的片头/片尾时间标记(客户端音频指纹自动学习上报) ==========
// 存储走 cacheManager KV(category='intro')——json/sqlite/memory 全兼容,不像历史同步只限 sqlite。
// 键 = 归一剧名|线路site_key(不同线路时间轴不同,不能混用);值 = { "<集号>|<通道>[|<部分>]": {os,oe,mv,pid,pend,bs,be,bmv,ed,emv,at} } 整剧一条。
// 必须按【集】存:每集冷开场长度不同,片头起点不同;不能按剧存一个时间。
// bs/be = 可选"开头贴片"区间(网络视听许可证/平台方片头贴片,与片头曲是两个独立可跳区间)。线上旧数据里的 v/bv/ev/src 留着不读。
// mv/emv = 片头/片尾是新算法算的,bmv = 贴片算法版本(3 才自动跳,2 只亮按钮)(合并规则见 lib/intro-marks);pid/pend = 学习对 id、待确认(第三集确认);miss/mt = 墓碑(这一集算不出来,1 定位不中 2 学不出 3 两样都不中)及时间。
// 部分 = 同一期的上/中/下(1/2/3),各用各的标记;老页面不带,写不到这些键上。
const { MARK_V: INTRO_MARK_V, BUMP_V: INTRO_BUMP_V, mergeOp: introMergeOp, mergeBump: introMergeBump, mergeOutro: introMergeOutro, applyMiss: introApplyMiss, settlePair: introSettlePair, marksForRead: introMarksForRead } = require('./lib/intro-marks');
const INTRO_TTL = 365 * 24 * 3600;   // 秒。每次写入续期
function introNormTitle(s) {
    // 与前端 _introTitleKey 保持一致：去括号内容/空格/标点,小写。改这里必须同步改前端。
    return String(s || '').replace(/[(（【\[][^)）】\]]*[)）】\]]/g, '').replace(/[\s·:：\-—_~～!！?？"'「」『』]/g, '').toLowerCase().slice(0, 60);
}
function introKey(title, site) { return introNormTitle(title) + '|' + String(site || '').slice(0, 40); }
const introLimiter = rateLimit({ windowMs: 60 * 1000, max: 60, keyGenerator: ipKey, message: { error: '请求过于频繁' } });

// 拉取某剧某线路的全部片头/片尾标记
app.get('/api/intro/marks', introLimiter, (req, res) => {
    const title = String(req.query.title || '').trim();
    if (!title) return res.json({ marks: {} });
    const map = cacheManager.get('intro', introKey(title, req.query.site)) || {};
    res.json({ marks: introMarksForRead(map) });
});

// 提交一集的片头/片尾标记(客户端音频指纹/包络自动学习)。登录站点即可提交(限流防刷)。
app.post('/api/intro/mark', introLimiter, (req, res) => {
    try {
        const b = req.body || {};
        // 站点配置了密码时要求有效 token(与历史同步同一套);未配密码的开放站不强求
        if (Object.keys(PASSWORD_HASH_MAP).length) {
            const u = PASSWORD_HASH_MAP[b.token];
            if (!u) return res.status(401).json({ error: 'Invalid token' });
            if (isBanned(b.token)) return res.status(403).json({ error: 'banned' });
        }
        const title = String(b.title || '').trim();
        const site = String(b.site || '').trim();
        const ep = parseInt(b.ep, 10);
        const opProvided = b.op_start != null || b.op_end != null;
        let os = Math.round(Number(b.op_start) * 10) / 10, oe = Math.round(Number(b.op_end) * 10) / 10;
        const hasOp = opProvided && isFinite(os) && isFinite(oe);
        let ed = b.ed_start == null ? null : Math.round(Number(b.ed_start) * 10) / 10;
        const dur = b.duration == null ? null : Math.round(Number(b.duration) * 10) / 10;
        // 🧭 时间轴通道:'f'=经去广告代理(贴片/中插已剔除) / 'r'=原始(直连/nofilter)。同一集两条通道时间轴差=被删广告时长,
        //    必须分开存(键 ep|ch),否则两边互相覆盖,观众看到的是另一条时间轴的值 → "跳过片头多跳二十秒"。
        //    老客户端不带 ch → 继续用裸 ep 键(老行为)。
        const ch = b.ch === 'f' || b.ch === 'r' ? b.ch : null;
        // 校验：ep 放宽到 8 位(综艺用日期做集号,如 20240105);片头起点前 25 分钟内、时长 10~240s(挡滥用载荷;曾是 150s,修掉中段掉窗后真实片头已到 144s,新页面超限按算不出记墓碑,不会反复重算)
        if (!title || !site || !Number.isInteger(ep) || ep < 0 || ep > 99999999) return res.status(400).json({ error: 'bad params' });
        if (opProvided && (!hasOp || os < 0 || oe <= os || os > 1500 || (oe - os) < 10 || (oe - os) > 240)) return res.status(400).json({ error: 'bad range' });
        const validDur = isFinite(dur) && dur > 0 && dur <= 6 * 3600 ? dur : null;
        if (ed != null && (!isFinite(ed) || ed <= 0 || ed > 6 * 3600 || (hasOp && ed <= oe) || (validDur && (ed < validDur * 0.45 || ed > validDur - 2)))) ed = null;
        // 可选"开头贴片"区间(网络视听许可证/平台方片头贴片):必须贴近片头部(起点≤120s)、3~90s、且在片头曲之前;非法就静默丢弃不拒整单
        let bs = b.b_start == null ? null : Math.round(Number(b.b_start) * 10) / 10;
        let be = b.b_end == null ? null : Math.round(Number(b.b_end) * 10) / 10;
        if (!hasOp || bs == null || be == null || !isFinite(bs) || !isFinite(be) || bs < 0 || bs > 120 || be <= bs || (be - bs) < 3 || (be - bs) > 90 || be > os + 5) { bs = null; be = null; }
        const key = introKey(title, site);
        const map = cacheManager.get('intro', key) || {};
        // 同一期的上/中/下各用各的标记:ep 已被日期式集号占满 8 位,所以部分单独进键。老页面不带这个字段,键不变
        const part = ch && (b.part === 1 || b.part === 2 || b.part === 3) ? b.part : 0;
        const epKey = ch ? (ep + '|' + ch + (part ? '|' + part : '')) : String(ep);
        const old = map[epKey];
        // 🧭 老页面留下的裸键(不带 ch)是每条通道读取时的兜底(m[ep|ch] || m[ep]),ep|ch 一落地就把它遮住了:只写一个墓碑或片尾,旧片头按钮和片尾就都没了。
        //    所以第一次写 ep|ch 要把裸键的内容带过来。片头值怎么合只看 ep|ch 自己(old);带上部分的键没有兜底,裸键分不清是上半还是下半
        const base = old || (ch && !part ? map[String(ep)] : undefined);
        if (ed != null && !hasOp && base && base.oe > base.os && ed <= base.oe) ed = null;
        const miss = !opProvided && (b.miss === 1 || b.miss === 2 || b.miss === 3) && b.mv === INTRO_MARK_V ? b.miss : 0;   // 🪦 墓碑只来自新页面,且不能夹带时间
        if (!hasOp && ed == null && !miss) return res.status(400).json({ error: 'bad range' });
        const mv2 = b.mv === INTRO_MARK_V;
        // 学习对 id:这一对算出来的标记和包络都带它,第三集确认只认它(见 lib/intro-marks)
        const pid = mv2 && typeof b.pid === 'string' && /^[a-z0-9]{4,24}$/.test(b.pid) ? b.pid : '';
        const pend = mv2 && b.pend === 1;
        const incBump = { bs, be, mv: mv2 ? INTRO_MARK_V : 0, bmv: mv2 && b.bmv === INTRO_BUMP_V ? INTRO_BUMP_V : 0, pend };
        const incOutro = { ed, emv: b.emv === INTRO_MARK_V ? INTRO_MARK_V : 0 };
        const now = Date.now();
        let rec;
        if (hasOp) rec = introMergeOp(old, { os, oe, mv: mv2 ? INTRO_MARK_V : 0, pid, pend }, now);
        else if (miss) rec = introApplyMiss(base, miss, now);
        else rec = { ...(base || {}), os: base?.os || 0, oe: base?.oe || 0, at: now };
        map[epKey] = introMergeOutro(introMergeBump(rec, base, incBump), base, incOutro);
        if (hasOp) introSettlePair(map, epKey, { mv: mv2 ? INTRO_MARK_V : 0, pid, pend });
        if (ch && map[epKey]) map[epKey].ch = ch;
        // 单剧集数上限(防灌爆一条 KV)
        const keys = Object.keys(map);
        if (keys.length > 500) { keys.sort((a, z) => (map[a].at || 0) - (map[z].at || 0)); for (const k of keys.slice(0, keys.length - 500)) delete map[k]; }
        cacheManager.set('intro', key, map, INTRO_TTL);
        res.json({ ok: true, mark: map[epKey] || null });
    } catch (e) {
        console.error('[Intro Mark Error]', e.message);
        res.status(500).json({ error: 'server error' });
    }
});

// ========== 🎵 片头/片尾音频包络云备份：客户端学习成果(10Hz响度包络,量化Uint8→base64,约1~2KB/段)存服务器 ==========
// 为什么值得存:marks 是"时间坐标",绑死线路时间轴,不能跨线路;包络是"剧集内容音频的形状",与时间轴无关——
//   A线路学出的片头曲包络,在B线路上滑动互相关(Pearson≥0.6 实测校验)就能"定位"出 B 自己的时间点。
//   于是①新设备/清了 localStorage 免两集冷启动(只抓本集定位,流量约减半);②资源站再多,一部剧全站只需学一次。
// 键 = 归一剧名|线路(每线路一条自洽记录:开头贴片是线路特有的,跟着记录走);GET 本线路没有→借同剧其它线路(borrowed),
//   借用的包络客户端必须实测定位命中才会转正回传登记到本线路,失配自动回退冷启动学习——坏/不匹配数据自灭,不会长期占坑。
const INTRO_ENV_TTL = 365 * 24 * 3600;   // 秒。每次写入/被采用回传都会续期
const INTRO_ENV_B64 = /^[A-Za-z0-9+/]+={0,2}$/;
const INTRO_ENV_DV = 2;   // 片头包络组件版本,与前端 IntroCore.ENV_DV 一致

// 拉取某剧某线路的包络;本线路没有时借同剧其它线路最新一条(borrowed=true)
app.get('/api/intro/env', introLimiter, (req, res) => {
    const title = String(req.query.title || '').trim();
    if (!title) return res.json({ env: null });
    const norm = introNormTitle(title);
    if (!norm) return res.json({ env: null });
    const site = String(req.query.site || '').slice(0, 40);
    // dv=新页面要的片头组件版本:本线路的片头是旧版时,顺带给一份别的线路的新版片头(片尾/贴片还用本线路的);老页面不带 dv,行为不变
    const wantDv = req.query.dv === String(INTRO_ENV_DV);
    const isNew = r => !!(r && r.d && r.dv === INTRO_ENV_DV);
    const exact = cacheManager.get('introenv', norm + '|' + site);
    if (exact && (!wantDv || isNew(exact))) return res.json({ env: exact, from: site, borrowed: false });
    let best = null, bestKey = '', bestNew = null, bestNewKey = '';
    for (const { key, value } of cacheManager.list('introenv', norm + '|')) {
        if (!value || value.v !== 2) continue;
        if ((value.at || 0) > (best ? best.at || 0 : -1)) { best = value; bestKey = key; }
        // 新版片头优先借最长的:短包络定位命中也只能跳短的一截,转正后还不会再重算(一样长才看新旧)
        const durNew = value.dur || 0, durBest = bestNew ? bestNew.dur || 0 : -1;
        if (isNew(value) && (durNew > durBest || (durNew === durBest && (value.at || 0) > (bestNew.at || 0)))) { bestNew = value; bestNewKey = key; }
    }
    if (exact) {
        const introBorrow = bestNew ? { dv: bestNew.dv, pid: bestNew.pid, peps: bestNew.peps, psite: bestNew.psite, pk: bestNew.pk, d: bestNew.d, sec: bestNew.sec, dur: bestNew.dur, maxStart: bestNew.maxStart || 0, from: bestNewKey.slice(norm.length + 1) } : undefined;
        return res.json({ env: exact, from: site, borrowed: false, introBorrow });
    }
    const pick = wantDv && bestNew ? bestNew : best, pickKey = wantDv && bestNew ? bestNewKey : bestKey;
    if (!pick) return res.json({ env: null });
    res.json({ env: pick, from: pickKey.slice(norm.length + 1), borrowed: true });
});

// 上传学习成果包络。env 字段与客户端本地记录同构:{v:2, dv, pid, peps, psite, pk, d,sec,dur,maxStart, bd,bdur,bdv, od,odur}
//   bdv=贴片包络算法版本(3 = 新算法学的,和标记的 bmv 同一个数):老页面传来的、没版本的 bd 盖不掉 bdv:3 的 bd;没版本的 bd 新页面定位出来只亮按钮
//   pid/peps=学出这条片头包络的学习对 id 和那两集的集号,在学习对之外的集定位命中才算确认(第三集确认,见 lib/intro-marks)。
//   psite/pk=学出它的线路、集号体系(d 日期 j 第N集 q 第N期):同一期在别的线路上可能是另一个数字,集号比得上才算确认,客户端判(IntroCore.pairWitness),转正登记到别的线路也不变。
//   dv=片头组件版本(新算法=2;片尾算法没变,贴片看 bdv,记录级 v 仍是 2,老页面照样能读能传):老页面传来的 d 盖不掉新版 d,新版 d 可以盖旧版 d。
//   d=片头曲包络 bd=开头贴片包络 od=片尾包络(都是 base64(Uint8) 10Hz 采样;量化不损 Pearson——尺度无关)。
// 组件级合并:来的组件覆盖,没带的组件保留旧值(先学出片头、后学出片尾的两次上传互不 clobber)。
app.post('/api/intro/env', introLimiter, (req, res) => {
    try {
        const b = req.body || {};
        if (Object.keys(PASSWORD_HASH_MAP).length) {
            const u = PASSWORD_HASH_MAP[b.token];
            if (!u) return res.status(401).json({ error: 'Invalid token' });
            if (isBanned(b.token)) return res.status(403).json({ error: 'banned' });
        }
        const title = String(b.title || '').trim();
        const site = String(b.site || '').trim().slice(0, 40);
        const e = b.env || {};
        if (!title || !introNormTitle(title) || !site || e.v !== 2) return res.status(400).json({ error: 'bad params' });
        // 逐组件校验:base64 字符集 + 长度上限(10Hz 包络≈10B/s;片头包络经跨空洞续接可到几百秒,给到 400s)
        //   + 秒数与包络字节数一致性(声称 150s 却只有 10s 数据的畸形载荷直接拒)
        const num = (x, lo, hi) => { const n = Math.round(Number(x) * 10) / 10; return isFinite(n) && n >= lo && n <= hi ? n : null; };
        const bytesOf = s => Math.floor(s.length * 3 / 4) - (s.endsWith('==') ? 2 : s.endsWith('=') ? 1 : 0);
        const b64 = (s, max, sec) => (typeof s === 'string' && s.length >= 40 && s.length <= max && INTRO_ENV_B64.test(s) && sec != null && Math.abs(bytesOf(s) / 10 - sec) <= 3) ? s : null;
        const rec = { v: 2, at: Date.now() };
        const sec = num(e.sec, 10, 400), dur = num(e.dur, 10, 250), d = b64(e.d, 5600, sec);
        if (d && dur) {
            rec.d = d; rec.sec = sec; rec.dur = dur; rec.maxStart = num(e.maxStart, 0, 1500) || 0;
            if (e.dv === INTRO_ENV_DV) {
                rec.dv = INTRO_ENV_DV;
                if (typeof e.pid === 'string' && /^[a-z0-9]{4,24}$/.test(e.pid) && Array.isArray(e.peps) && e.peps.length === 2 && e.peps.every(x => Number.isInteger(x) && x >= 0 && x <= 99999999)) {
                    rec.pid = e.pid; rec.peps = e.peps;
                    if (typeof e.psite === 'string' && e.psite.length >= 1 && e.psite.length <= 40) rec.psite = e.psite;
                    if (e.pk === 'd' || e.pk === 'j' || e.pk === 'q') rec.pk = e.pk;
                }
            }
        }
        const bdur = num(e.bdur, 3, 90), bd = b64(e.bd, 1200, bdur);
        if (bd) { rec.bd = bd; rec.bdur = bdur; if (e.bdv === INTRO_BUMP_V) rec.bdv = INTRO_BUMP_V; }
        const odur = num(e.odur, 10, 160), od = b64(e.od, 2400, odur);
        if (od) { rec.od = od; rec.odur = odur; }
        if (!rec.d && !rec.od) return res.status(400).json({ error: 'no payload' });
        const key = introNormTitle(title) + '|' + site;
        const old = cacheManager.get('introenv', key);
        if (old && old.v === 2) {
            if (old.d && (!rec.d || (old.dv === INTRO_ENV_DV && rec.dv !== INTRO_ENV_DV))) {
                rec.d = old.d; rec.sec = old.sec; rec.dur = old.dur; rec.maxStart = old.maxStart || 0;
                if (old.dv) rec.dv = old.dv; else delete rec.dv;
                if (old.pid) { rec.pid = old.pid; rec.peps = old.peps; if (old.psite) rec.psite = old.psite; if (old.pk) rec.pk = old.pk; }
            }
            if (old.bd && (!rec.bd || (old.bdv === INTRO_BUMP_V && rec.bdv !== INTRO_BUMP_V))) { rec.bd = old.bd; rec.bdur = old.bdur; if (old.bdv) rec.bdv = old.bdv; else delete rec.bdv; }
            if (!rec.od && old.od) { rec.od = old.od; rec.odur = old.odur; }
        }
        cacheManager.set('introenv', key, rec, INTRO_ENV_TTL);
        res.json({ ok: true });
    } catch (e) {
        console.error('[Intro Env Error]', e.message);
        res.status(500).json({ error: 'server error' });
    }
});

// ========== 求片 API（用户提交想看的剧；站长后台贴磁力/下载链接履行）==========
const ADMIN_TOKEN = process.env.ADMIN_TOKEN || '';
const REQ_DB_OK = () => cacheManager.type === 'sqlite' && cacheManager.db;

// ========== 用户统计/封禁 助手 ==========
// 记录用户活跃(last_active)、登录(last_login)、身份标签(label=email)。在历史同步/求片/登录处调用。
function touchUser(token, opts) {
    opts = opts || {};
    if (!REQ_DB_OK() || !token) return;
    try {
        const now = Date.now();
        const exists = cacheManager.db.prepare('SELECT 1 FROM user_stats WHERE user_token = ?').get(token);
        if (exists) {
            // first_seen 可能为空(后台封禁时给没记录的 token 插的行),第一次真活跃时补上
            cacheManager.db.prepare('UPDATE user_stats SET last_active = ?, first_seen = COALESCE(first_seen, ?), last_login = COALESCE(?, last_login), label = COALESCE(?, label) WHERE user_token = ?')
                .run(now, now, opts.login ? now : null, (opts.label && String(opts.label).trim()) ? String(opts.label).trim() : null, token);
        } else {
            cacheManager.db.prepare('INSERT INTO user_stats (user_token, label, first_seen, last_login, last_active, banned) VALUES (?, ?, ?, ?, ?, 0)')
                .run(token, (opts.label && String(opts.label).trim()) ? String(opts.label).trim() : null, now, opts.login ? now : null, now);
        }
    } catch (e) { /* 统计失败不影响主流程 */ }
}
function isBanned(token) {
    if (!REQ_DB_OK() || !token) return false;
    try { const r = cacheManager.db.prepare('SELECT banned FROM user_stats WHERE user_token = ?').get(token); return !!(r && r.banned); }
    catch (e) { return false; }
}
// 恒定时间比较 ADMIN_TOKEN（后台接口会吐出全站独立密码明文，避免计时侧信道猜令牌）
function adminTokenMatch(provided) {
    if (!ADMIN_TOKEN || !provided) return false;
    const a = Buffer.from(String(provided)), b = Buffer.from(ADMIN_TOKEN);
    if (a.length !== b.length) return false;
    try { return crypto.timingSafeEqual(a, b); } catch (e) { return false; }
}

// 求片海报只收 TMDB:路径 '/xxx.jpg' 或 image.tmdb.org 的完整地址(统一存成路径,后台经 /api/tmdb-image 代理显示)。
//   其它地址一律存空 —— 后台会渲染海报,任意外链 = 站长一打开求片页,IP/UA/查看时间就送到提交者的服务器。
//   文件名规则与 /api/tmdb-image 的白名单一致。
function tmdbPosterPath(p) {
    const s = String(p || '').trim();
    if (/^\/[A-Za-z0-9]+\.(jpg|jpeg|png|webp)$/i.test(s)) return s;
    const m = s.match(/^https?:\/\/image\.tmdb\.org\/t\/p\/[A-Za-z0-9]+\/([A-Za-z0-9]+\.(?:jpg|jpeg|png|webp))$/i);
    return m ? '/' + m[1] : '';
}

// 提交求片（需登录账号）
app.post('/api/requests', (req, res) => {
    if (!ADMIN_TOKEN) return res.status(403).json({ error: '求片功能未开启' });  // 未配 ADMIN_TOKEN = 功能关闭
    const { token, name, tmdb_id, poster, note, label, year, aka, cast } = req.body || {};
    if (!token || !name || !String(name).trim()) return res.status(400).json({ error: 'Missing token or name' });
    if (!PASSWORD_HASH_MAP[token]) return res.status(401).json({ error: 'Invalid token' });
    if (isBanned(token)) return res.status(403).json({ error: 'banned', banned: true });
    if (!REQ_DB_OK()) return res.json({ ok: false, message: 'SQLite not available' });
    touchUser(token, { label });  // 记录活跃 + 身份标签(email)
    try {
        // 防刷：单用户待处理(pending)上限 3
        const pending = cacheManager.db.prepare("SELECT COUNT(*) c FROM content_requests WHERE user_token = ? AND status = 'pending'").get(token).c;
        if (pending >= 3) return res.status(429).json({ error: '最多同时有 3 条待处理的求片，请等已有的处理完或先撤销' });
        const now = Date.now();
        const info = cacheManager.db.prepare(`INSERT INTO content_requests (user_token, user_label, name, tmdb_id, poster, note, year, aka, cast_info, status, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'pending', ?, ?)`).run(
            token, String(label || '').slice(0, 120), String(name).trim().slice(0, 200),
            String(tmdb_id || '').slice(0, 40), tmdbPosterPath(poster), String(note || '').slice(0, 500),
            String(year || '').slice(0, 20), String(aka || '').slice(0, 200), String(cast || '').slice(0, 200), now, now);
        if (userStats) userStats.invalidate();   // 📊 后台概览/用户列表的求片数有 20s 缓存
        res.json({ ok: true, id: info.lastInsertRowid });
    } catch (e) { console.error('[求片提交]', e.message); res.status(500).json({ error: 'Database error' }); }
});

// 撤销自己的求片（仅限本人；pending 或 need_info 可撤销）→ 让"上限 3"不至于把人卡死，
// 也用于 need_info 补充重提时清掉旧的那条（避免同片堆积孤儿记录）。已履行/已拒绝的不可删。
app.post('/api/requests/cancel', (req, res) => {
    const { token, id } = req.body || {};
    if (!token || !PASSWORD_HASH_MAP[token]) return res.status(401).json({ error: 'Invalid token' });
    if (isBanned(token)) return res.status(403).json({ error: 'banned', banned: true });
    if (!REQ_DB_OK() || !id) return res.status(400).json({ error: 'Bad request' });
    try {
        const info = cacheManager.db.prepare("DELETE FROM content_requests WHERE id = ? AND user_token = ? AND status IN ('pending', 'need_info')").run(id, token);
        if (info.changes && userStats) userStats.invalidate();
        res.json({ ok: true, deleted: info.changes });
    } catch (e) { res.status(500).json({ error: 'Database error' }); }
});

// 我的求片
app.get('/api/requests/mine', (req, res) => {
    const token = req.query.token;
    if (!token || !PASSWORD_HASH_MAP[token]) return res.status(401).json({ error: 'Invalid token' });
    if (isBanned(token)) return res.status(403).json({ error: 'banned', banned: true });
    if (!REQ_DB_OK()) return res.json({ requests: [] });
    try {
        const rows = cacheManager.db.prepare(`SELECT id, name, tmdb_id, poster, note, year, aka, cast_info, status, fulfill_link, fulfill_note, created_at, updated_at
            FROM content_requests WHERE user_token = ? ORDER BY created_at DESC LIMIT 100`).all(token);
        res.json({ requests: rows });
    } catch (e) { res.status(500).json({ error: 'Database error' }); }
});

// 站长：列出全部求片（用 ADMIN_TOKEN 鉴权）
app.get('/api/requests/admin', (req, res) => {
    // 优先从请求头取令牌(避免 ADMIN_TOKEN 落入访问日志/Referer/浏览器历史)；兼容旧的 query 传参
    const admin = req.headers['x-admin-token'] || req.query.admin;
    if (!adminTokenMatch(admin)) return res.status(403).json({ error: 'Forbidden' });
    if (!REQ_DB_OK()) return res.json({ requests: [] });
    try {
        const status = req.query.status;
        const rows = status
            ? cacheManager.db.prepare(`SELECT * FROM content_requests WHERE status = ? ORDER BY created_at DESC LIMIT 500`).all(status)
            : cacheManager.db.prepare(`SELECT * FROM content_requests ORDER BY (status='pending') DESC, created_at DESC LIMIT 500`).all();
        // 加上求片人身份(邮箱/独立密码/token前缀)，方便站长确认是谁提的
        rows.forEach(r => { r.identity = userIdentity(r.user_token, r.user_label); });
        res.json({ requests: rows });
    } catch (e) { res.status(500).json({ error: 'Database error' }); }
});

// 站长：履行/更新求片（贴链接、改状态、删除）
app.post('/api/requests/admin', (req, res) => {
    const { admin, id, action, status, fulfill_link, fulfill_note } = req.body || {};
    if (!adminTokenMatch(admin)) return res.status(403).json({ error: 'Forbidden' });
    if (!REQ_DB_OK() || !id) return res.status(400).json({ error: 'Bad request' });
    try {
        // 📊 改完都清统计缓存:否则后台概览"待处理求片"、用户的求片数要过 20s 才变(批量接口/封禁早就清了)
        if (action === 'delete') {
            cacheManager.db.prepare('DELETE FROM content_requests WHERE id = ?').run(id);
            if (userStats) userStats.invalidate();
            return res.json({ ok: true, deleted: true });
        }
        const st = ['pending', 'fulfilled', 'rejected', 'need_info'].includes(status) ? status : 'fulfilled';
        const prev = cacheManager.db.prepare('SELECT user_token, name, status FROM content_requests WHERE id = ?').get(id);
        cacheManager.db.prepare(`UPDATE content_requests SET status = ?, fulfill_link = ?, fulfill_note = ?, updated_at = ? WHERE id = ?`)
            .run(st, String(fulfill_link || '').slice(0, 2000), String(fulfill_note || '').slice(0, 500), Date.now(), id);
        if (userStats) userStats.invalidate();
        // 🔔 状态真的变了才推送(只改链接/说明不打扰)
        if (prev && prev.status !== st) notifyRequestStatus({ id, user_token: prev.user_token, name: prev.name, from: prev.status, to: st });
        res.json({ ok: true });
    } catch (e) { console.error('[求片履行]', e.message); res.status(500).json({ error: 'Database error' }); }
});

// ========== 站长后台：用户统计 / 封禁（均 ADMIN_TOKEN 鉴权，仅 网址#admin 用得到）==========
const adminAuthed = (req) => {
    const t = req.headers['x-admin-token'] || req.query.admin || (req.body && req.body.admin);
    return adminTokenMatch(t);
};

// 用户统计列表/概览/详情 → 见 lib/user-stats(GET /api/admin/users|overview|user|shares|requests,SQL 聚合 + 20s 缓存)。
// 旧实现同步 JSON.parse 最多 20 万行 user_history 估算时长,会阻塞事件循环把全站一起卡死,已删除。

// 封禁 / 解封（被封用户：/api/config 返回 banned→前端锁屏；历史同步/求片接口一律 403）
app.post('/api/admin/ban', (req, res) => {
    if (!adminAuthed(req)) return res.status(403).json({ error: 'Forbidden' });
    if (!REQ_DB_OK()) return res.status(400).json({ error: 'SQLite not available' });
    const { token, banned } = req.body || {};
    if (!token) return res.status(400).json({ error: 'Missing token' });
    try {
        const b = banned ? 1 : 0, now = Date.now();
        const exists = cacheManager.db.prepare('SELECT 1 FROM user_stats WHERE user_token = ?').get(token);
        if (exists) cacheManager.db.prepare('UPDATE user_stats SET banned = ?, banned_at = ? WHERE user_token = ?').run(b, b ? now : null, token);
        // 没有统计行的老用户(只有旧同步历史/求片):不能写 first_seen/last_active = now —— 后台会把这个封禁的沉睡用户算成"今日活跃""7 日新增"。
        //   last_active 留空;first_seen 取他最早的同步历史/求片时间(都没有就留空)
        else cacheManager.db.prepare(`INSERT INTO user_stats (user_token, first_seen, banned, banned_at) VALUES (?, (SELECT MIN(t) FROM (
                SELECT MIN(updated_at) t FROM user_history WHERE user_token = ?
                UNION ALL SELECT MIN(created_at) FROM content_requests WHERE user_token = ?)), ?, ?)`).run(token, token, token, b, b ? now : null);
        if (userStats) userStats.invalidate();   // 📊 用户列表有 20s 缓存,封禁/解封要立刻反映
        res.json({ ok: true, banned: !!b });
    } catch (e) { res.status(500).json({ error: 'Database error' }); }
});

// 某用户的观看记录（站长 drill-in 看详情）
app.get('/api/admin/user-history', (req, res) => {
    if (!adminAuthed(req)) return res.status(403).json({ error: 'Forbidden' });
    if (!REQ_DB_OK()) return res.json({ history: [] });
    const token = req.query.token;
    if (!token) return res.status(400).json({ error: 'Missing token' });
    try {
        const rows = cacheManager.db.prepare('SELECT item_id, item_data, updated_at FROM user_history WHERE user_token = ? ORDER BY updated_at DESC LIMIT 300').all(token);
        const history = rows.map(r => {
            let d = {}; try { d = JSON.parse(r.item_data) || {}; } catch (e) { }
            return {
                name: d.name || r.item_id, episode: d.episode || null, progress: d.progress || 0,
                progressTime: d.progressTime || 0, progressDuration: d.progressDuration || 0,
                watchedAt: d.watchedAt || null, updated_at: r.updated_at
            };
        });
        res.json({ history });
    } catch (e) { res.status(500).json({ error: 'Database error' }); }
});

// TMDB 通用代理与缓存 API
const TMDB_CACHE_TTL = 3600 * 10; // 缓存 10 小时
// /tv/{id}(不带 append_to_response)= 追更日历读 next_episode_to_air:只缓存 1 小时 ——
//   前端自己还缓存 6 小时,这里缓存 10 小时会让"下一集"最长旧 16 小时(播出日过了还报"今天更新"、延播了还报原来那天)。
//   /tv/{id}/season/{n}(/episode/{e})同理:只在 next_episode_to_air 还停在昨天那集时才查(按集往后找 ≥ 今天的那集),排期也会改
function tmdbCacheTtl(p, params) {
    return /^\/tv\/\d+(\/season\/\d+(\/episode\/\d+)?)?$/.test(String(p || '')) && !(params && params.append_to_response) ? 3600 : TMDB_CACHE_TTL;
}
app.get('/api/tmdb-proxy', async (req, res) => {
    const { path: tmdbPath, ...params } = req.query;

    if (!tmdbPath) return res.status(400).json({ error: 'Missing path' });

    const TMDB_API_KEY = process.env.TMDB_API_KEY;
    if (!TMDB_API_KEY) return res.status(500).json({ error: 'API Key not configured' });

    // 构建唯一的缓存 Key (排序参数以确保 Key 稳定)
    const sortedParams = Object.keys(params).sort().map(k => `${k}=${params[k]}`).join('&');
    const cacheKey = `tmdb_proxy_${tmdbPath}_${sortedParams}`;

    const cached = cacheManager.get('detail', cacheKey);
    if (cached) {
        // console.log(`[TMDB Proxy] Cache Hit: ${cacheKey}`);
        return res.json(cached);
    }

    try {
        // 判断是否来自中国大陆（支持 X-Client-Public-IP 头和私有 IP 检测）
        const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];

        // 只有配置了代理 URL 且用户来自中国大陆时，才使用代理
        let useProxy = false;
        if (TMDB_PROXY_URL) {
            useProxy = await isChineseIP(req);
        }

        const TMDB_BASE = useProxy
            ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3`  // 代理需要 /api/3 前缀
            : 'https://api.themoviedb.org/3';  // 海外用户直连官方 API

        // tmdbPath 格式如 /trending/all/week, /discover/movie 等
        const finalUrl = `${TMDB_BASE}${tmdbPath}`;

        const response = await axios.get(finalUrl, {
            params: {
                ...params,
                api_key: TMDB_API_KEY,
                language: 'zh-CN'
            },
            timeout: 15000  // 增加超时时间到 15 秒（代理可能较慢）
        });

        // 缓存结果
        cacheManager.set('detail', cacheKey, response.data, tmdbCacheTtl(tmdbPath, params));
        res.json(response.data);
    } catch (error) {
        console.error(`[TMDB Proxy Error] ${tmdbPath}:`, error.message);
        res.status(error.response?.status || 500).json({ error: 'Proxy request failed' });
    }
});

// 远程站点配置(REMOTE_DB_URL):缓存 5 分钟内直接用,否则拉一次;拉到 → 写缓存并返回,拉不到 → null(调用方自己决定回退)。
//   /api/sites 与收藏后台检查(lib/favorites 的 loadSites)共用:以前只有 /api/sites 会拉,重启后没人打开首页时
//   getDB() 一直读本地模板,收藏检查把所有到期行当"站点已删除"推迟一天
async function loadRemoteDb() {
    if (!REMOTE_DB_URL) return null;
    const now = Date.now();
    if (remoteDbCache && now - remoteDbLastFetch < REMOTE_DB_CACHE_TTL) return remoteDbCache;
    try {
        const response = await axios.get(REMOTE_DB_URL, { timeout: 10000, proxy: false });   // 🎯 本地定制：proxy:false 直连，消除走 mihomo 代理超时
        if (response.data && Array.isArray(response.data.sites)) {
            remoteDbCache = response.data;
            remoteDbLastFetch = now;
            console.log('[Remote] Config loaded successfully');
            return remoteDbCache;
        }
    } catch (err) {
        console.error('[Remote] Failed to load config:', err.message);
    }
    return null;
}

// 黄果封面解密代理：站点图片是 AES-128-CBC 加密字节，浏览器无法直接显示
const HUANGGUO_IMG_KEY = Buffer.from('f5d965df75336270', 'utf8');
const HUANGGUO_IMG_IV = Buffer.from('97b60394abc2fbe1', 'utf8');
// 黄果会不定期切换图片 CDN；这些域名返回 AES 加密图片字节，必须经本站解密。
const EXT_IMAGE_ALLOWED_HOST_SUFFIXES = ['.eanfog.cn', '.nkgjoa.cn', '.zdmhyg.cn'];

function isAllowedExtImageUrl(rawUrl) {
    try {
        const u = new URL(rawUrl);
        if (!['http:', 'https:'].includes(u.protocol)) return false;
        const host = u.hostname.toLowerCase();
        return EXT_IMAGE_ALLOWED_HOST_SUFFIXES.some(suffix =>
            host === suffix.slice(1) || host.endsWith(suffix)
        );
    } catch (e) {
        return false;
    }
}

function detectImageType(buf) {
    if (!buf || buf.length < 8) return null;
    if (buf[0] === 0xff && buf[1] === 0xd8) return { ext: 'jpg', contentType: 'image/jpeg' };
    if (buf.subarray(0, 8).equals(Buffer.from('89504e470d0a1a0a', 'hex'))) return { ext: 'png', contentType: 'image/png' };
    if (buf.length >= 12 && buf.toString('ascii', 0, 4) === 'RIFF' && buf.toString('ascii', 8, 12) === 'WEBP') {
        return { ext: 'webp', contentType: 'image/webp' };
    }
    const gif = buf.toString('ascii', 0, 6);
    if (gif === 'GIF87a' || gif === 'GIF89a') return { ext: 'gif', contentType: 'image/gif' };
    return null;
}

function trimDecodedImage(buf, type) {
    if (!buf || !type) return buf;
    if (type.ext === 'jpg') {
        const end = buf.lastIndexOf(Buffer.from([0xff, 0xd9]));
        if (end >= 0) return buf.subarray(0, end + 2);
    } else if (type.ext === 'png') {
        const endSig = Buffer.from('49454e44ae426082', 'hex');
        const end = buf.lastIndexOf(endSig);
        if (end >= 0) return buf.subarray(0, end + endSig.length);
    }
    return buf;
}

function decryptHuangguoImage(raw) {
    const directType = detectImageType(raw);
    if (directType) return { data: trimDecodedImage(raw, directType), type: directType };
    if (!raw || raw.length === 0 || raw.length % 16 !== 0) return null;

    try {
        const decipher = crypto.createDecipheriv('aes-128-cbc', HUANGGUO_IMG_KEY, HUANGGUO_IMG_IV);
        decipher.setAutoPadding(false);
        let decoded = Buffer.concat([decipher.update(raw), decipher.final()]);
        const type = detectImageType(decoded);
        if (!type) return null;

        // 去掉 PKCS#7 padding（站点有时也会在图片终止符后追加固定字节）
        const pad = decoded[decoded.length - 1];
        if (pad >= 1 && pad <= 16) {
            let valid = true;
            for (let i = decoded.length - pad; i < decoded.length; i++) {
                if (decoded[i] !== pad) { valid = false; break; }
            }
            if (valid) decoded = decoded.subarray(0, decoded.length - pad);
        }
        decoded = trimDecodedImage(decoded, type);
        return { data: decoded, type };
    } catch (e) {
        return null;
    }
}

app.get('/api/ext-image-proxy', async (req, res) => {
    const rawUrl = req.query.url;
    if (!rawUrl || !isAllowedExtImageUrl(rawUrl)) {
        return res.status(400).json({ error: 'Invalid or disallowed image URL' });
    }

    const stableUrl = new URL(rawUrl);
    stableUrl.search = '';
    const upstreamUrl = stableUrl.toString();
    const cacheId = crypto.createHash('sha256').update(upstreamUrl).digest('hex');
    const cacheDataPath = path.join(EXT_IMAGE_CACHE_DIR, cacheId + '.img');
    const cacheMetaPath = path.join(EXT_IMAGE_CACHE_DIR, cacheId + '.json');

    try {
        if (!process.env.VERCEL && fs.existsSync(cacheDataPath) && fs.existsSync(cacheMetaPath)) {
            const meta = JSON.parse(fs.readFileSync(cacheMetaPath, 'utf8'));
            const data = fs.readFileSync(cacheDataPath);
            res.set('Content-Type', meta.contentType || 'image/jpeg');
            res.set('Cache-Control', 'public, max-age=604800, immutable');
            return res.send(data);
        }

        const response = await axios.get(upstreamUrl, {
            timeout: 20000,
            responseType: 'arraybuffer',
            proxy: false,
            maxRedirects: 3,
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                'Referer': 'https://huangguoai.com/',
                'Accept': 'image/avif,image/webp,image/apng,image/*,*/*;q=0.8',
                'Accept-Encoding': 'identity'
            }
        });
        const raw = Buffer.from(response.data);
        const decoded = decryptHuangguoImage(raw);
        if (!decoded) {
            return res.status(502).json({ error: 'Image decryption failed' });
        }

        if (!process.env.VERCEL) {
            fs.writeFileSync(cacheDataPath, decoded.data);
            fs.writeFileSync(cacheMetaPath, JSON.stringify({ contentType: decoded.type.contentType }));
        }
        res.set('Content-Type', decoded.type.contentType);
        res.set('Cache-Control', 'public, max-age=604800, immutable');
        res.send(decoded.data);
    } catch (err) {
        console.error(`[Ext Image Proxy] ${upstreamUrl.substring(0, 100)}:`, err.message);
        res.status(502).json({ error: 'Image proxy failed' });
    }
});

// 扩展源 HLS / MP4 同源代理：中转 m3u8、AES 密钥和 TS 分片，解决客户端网络/CORS/防盗链问题
function isAllowedExtHlsUrl(rawUrl) {
    try {
        const u = new URL(rawUrl);
        if (!['http:', 'https:'].includes(u.protocol)) return false;
        const host = u.hostname.toLowerCase();
        // 阻止环回地址和本地内网，保障安全
        if (host === 'localhost' || host === '127.0.0.1' || host.startsWith('192.168.') || host.startsWith('10.') || host.startsWith('172.16.')) {
            return false;
        }
        return true;
    } catch (e) {
        return false;
    }
}

function makeExtHlsProxyUrl(rawUrl, isKey = false) {
    let proxyName = isKey ? 'crypt.key' : 'segment.ts';
    try {
        const pathname = new URL(rawUrl).pathname.toLowerCase();
        if (pathname.includes('.m3u8')) proxyName = 'stream.m3u8';
        else if (pathname.endsWith('.ts')) proxyName = 'segment.ts';
        else if (pathname.endsWith('.key') || isKey) proxyName = 'crypt.key';
        else if (pathname.endsWith('.aac')) proxyName = 'audio.aac';
        else if (pathname.endsWith('.m4s')) proxyName = 'segment.m4s';
        else if (pathname.endsWith('.mp4')) proxyName = 'segment.mp4';
    } catch (e) { /* 使用默认 segment.ts */ }
    // 路径保留媒体扩展名，兼容会校验分片后缀的 HLS 客户端 (如 ffmpeg / ExoPlayer / Safari)
    return `/api/ext-hls-proxy/${proxyName}?url=${encodeURIComponent(rawUrl)}`;
}

function rewriteExtHlsManifest(text, upstreamUrl) {
    return String(text || '').split(/\r?\n/).map(line => {
        const trimmed = line.trim();
        if (!trimmed) return line;

        // #EXT-X-KEY / #EXT-X-MAP 等标签中的 URI="..."
        if (trimmed.startsWith('#')) {
            return line.replace(/URI=(['"])([^'"]+)\1/g, (all, quote, uri) => {
                try {
                    const absolute = new URL(uri, upstreamUrl).toString();
                    return isAllowedExtHlsUrl(absolute)
                        ? `URI=${quote}${makeExtHlsProxyUrl(absolute, true)}${quote}`
                        : all;
                } catch (e) {
                    return all;
                }
            });
        }

        // 普通分片或子清单行
        try {
            const absolute = new URL(trimmed, upstreamUrl).toString();
            return isAllowedExtHlsUrl(absolute) ? makeExtHlsProxyUrl(absolute, false) : line;
        } catch (e) {
            return line;
        }
    }).join('\n');
}

// 快速内存缓存：解析好的短剧单集直链（短 TTL，避免重复解析）
const extPlayinfoCache = new Map();
// 播放直链通常包含短期鉴权参数；15 分钟能覆盖一轮连续观看，同时避免长期使用过期 URL。
const EXT_PLAYINFO_CACHE_TTL = 900000;
const extResolveInflight = new Map();
const extManifestCache = new Map();
const EXT_MANIFEST_CACHE_TTL = 120000;

// 🧊 P0-2 磁盘化播放缓存：内存 Map 只作热层，冷数据走 SQLite(cache.db, 重启不冷)。
// 仅当缓存类型为 sqlite/json 且非 Vercel Serverless 时启用（内存/无 模式跳过）。
const EXT_DISK_CACHE_ENABLED = !process.env.VERCEL && (CACHE_TYPE === 'sqlite' || CACHE_TYPE === 'json');
const EXT_DISK_CACHE_TTL_SEC = 900; // 15 分钟，与内存 playinfo TTL 对齐

function getDiskExt(key) {
    if (!EXT_DISK_CACHE_ENABLED || !cacheManager) return null;
    try { return cacheManager.get('ext_media', key); } catch (e) { return null; }
}
function setDiskExt(key, value) {
    if (!EXT_DISK_CACHE_ENABLED || !cacheManager) return;
    try { cacheManager.set('ext_media', key, value, EXT_DISK_CACHE_TTL); } catch (e) { }
}

function getCachedExtManifest(url) {
    const item = extManifestCache.get(url);
    if (!item) return null;
    if (Date.now() - item.time > EXT_MANIFEST_CACHE_TTL) {
        extManifestCache.delete(url);
        return null;
    }
    return item.text;
}
function setCachedExtManifest(url, text) {
    if (!url || !text) return;
    extManifestCache.set(url, { text, time: Date.now() });
    setDiskExt('m:' + url, { k: 'm', text }); // 落盘（重启不冷）
    if (extManifestCache.size > 300) extManifestCache.delete(extManifestCache.keys().next().value);
}
function getCachedExtManifestCold(url) {
    const hot = getCachedExtManifest(url);
    if (hot) return hot;
    const cold = getDiskExt('m:' + url);
    if (cold && cold.k === 'manifest' && typeof cold.text === 'string') {
        setCachedExtManifest(url, cold.text);
        return cold.text;
    }
    return null;
}
function getCachedExtPlayinfo(url) {
    const item = extPlayinfoCache.get(url);
    if (!item) return null;
    if (Date.now() - item.time > EXT_PLAYINFO_CACHE_TTL) {
        extPlayinfoCache.delete(url);
        return null;
    }
    return item.m3u8;
}
function setCachedExtPlayinfo(url, m3u8) {
    if (url && m3u8) {
        extPlayinfoCache.set(url, { m3u8, time: Date.now() });
        setDiskExt('p:' + url, { k: 'playinfo', m3u8 }); // 落盘（重启不冷）
        if (extPlayinfoCache.size > 500) {
            const firstKey = extPlayinfoCache.keys().next().value;
            extPlayinfoCache.delete(firstKey);
        }
    }
}
function getCachedExtPlayinfoCold(url) {
    const hot = getCachedExtPlayinfo(url);
    if (hot) return hot;
    const cold = getDiskExt('p:' + url);
    if (cold && cold.k === 'playinfo' && /^https?:\/\//i.test(String(cold.m3u8))) {
        setCachedExtPlayinfo(url, cold.m3u8);
        return cold.m3u8;
    }
    return null;
}

// 扩展源单集播放直链解析：优先内存热层，冷读可走 SQLite 磁盘恢复，inflight 去重防并发重复解析。
async function resolveExtMediaUrl(site, rawUrl, playArgs = {}) {
    const cached = getCachedExtPlayinfoCold(rawUrl);
    if (cached) return { url: cached, cached: true };

    let promise = extResolveInflight.get(rawUrl);
    if (!promise) {
        promise = (async () => {
            const epMatch = rawUrl.match(/\/ep-(\d+)\/?/);
            const ep = epMatch ? epMatch[1] : String(playArgs.ep || '1');
            const pi = await runExtJs(site, 'getPlayinfo', { ...playArgs, url: rawUrl, ep });
            const resolved = extPlayinfoToVodUrl(pi);
            if (!resolved || !/^https?:\/\//i.test(resolved)) throw new Error('Unable to resolve media URL');
            setCachedExtPlayinfo(rawUrl, resolved);
            return resolved;
        })().finally(() => extResolveInflight.delete(rawUrl));
        extResolveInflight.set(rawUrl, promise);
    }
    return { url: await promise, cached: false };
}

// 预取某集 m3u8 清单进缓存：让 /api/ext-hls-proxy 后续请求直接命中缓存，省一次上游清单请求。
// 用于首页卡片、详情返回后的后台预热，加速“点开即播”与“切集连播”。
function warmExtManifest(siteKey, mediaUrl) {
    try {
        if (!mediaUrl || !/\.m3u8/i.test(String(mediaUrl))) return;
        const u = `http://127.0.0.1:${PORT}/api/ext-hls-proxy/stream.m3u8?site_key=${encodeURIComponent(String(siteKey || '').toLowerCase())}&url=${encodeURIComponent(mediaUrl)}`;
        fetch(u, { signal: AbortSignal.timeout(15000) }).then(r => r.text()).catch(() => { });
    } catch (e) { }
}

// 扩展源单集播放页解析：前端切换任意集时先解析真实媒体 URL，
// 从而正确区分河马 MP4 与 AGE/黄果 HLS，避免把 MP4 误交给 Hls.js。
app.get('/api/ext/resolve-play', async (req, res) => {
    const siteKey = String(req.query.site_key || '').toLowerCase();
    const rawUrl = String(req.query.url || '');
    if (!siteKey || !rawUrl || !isAllowedExtHlsUrl(rawUrl)) {
        return res.status(400).json({ error: 'Invalid resolve request' });
    }

    const cached = getCachedExtPlayinfoCold(rawUrl);
    if (cached) {
        return res.json({ url: cached, type: /\.mp4(?:[?#]|$)/i.test(cached) ? 'auto' : 'hls', cached: true });
    }

    const site = getDB().sites.find(s => String(s.key || '').toLowerCase() === siteKey && isExtSite(s));
    if (!site) return res.status(404).json({ error: 'Ext site not found' });

    try {
        const result = await resolveExtMediaUrl(site, rawUrl, { ep: req.query.ep || '1' });
        const resolved = result.url;
        return res.json({ url: resolved, type: /\.mp4(?:[?#]|$)/i.test(resolved) ? 'auto' : 'hls', cached: result.cached });
    } catch (e) {
        console.error(`[Ext Resolve Play] ${siteKey}:`, e.message);
        return res.status(502).json({ error: 'Resolve failed' });
    }
});

app.get(['/api/ext-hls-proxy', '/api/ext-hls-proxy/:resource'], async (req, res) => {
    let rawUrl = req.query.url;
    if (!rawUrl || !isAllowedExtHlsUrl(rawUrl)) {
        return res.status(400).json({ error: 'Invalid or disallowed HLS URL' });
    }

    try {
        // 如果传入的是视频播放页面 URL (例如 https://huangguoai.com/video/3444/ep-2/)，动态解析其 m3u8 直链
        if (!rawUrl.includes('.m3u8') && !rawUrl.endsWith('.ts') && !rawUrl.endsWith('.key')) {
            const cachedM3u8 = getCachedExtPlayinfoCold(rawUrl);
            if (cachedM3u8) {
                rawUrl = cachedM3u8;
            } else {
                const sites = getDB().sites;
                const requestedSiteKey = String(req.query.site_key || '').toLowerCase();
                // 必须按当前卡片所属扩展源解析，不能总是取列表里的第一个扩展源。
                // 旧逻辑会用黄果脚本解析河马/AGE 的第2集播放页，最终把 HTML 当成 HLS 返回。
                const site = requestedSiteKey
                    ? sites.find(s => String(s.key || '').toLowerCase() === requestedSiteKey && isExtSite(s))
                    : sites.find(s => {
                        const key = String(s.key || '').toLowerCase();
                        if (!isExtSite(s)) return false;
                        if (key === 'huangguo') return rawUrl.includes('huangguoai.com');
                        if (key === 'kuaikaw') return rawUrl.includes('kuaikaw.cn');
                        if (key === 'age') return rawUrl.includes('agedm.io') || rawUrl.includes('wuzhoupai.com');
                        if (key === 'ppnix') return rawUrl.includes('ppnix.com');
                        return false;
                    });
                if (site) {
                    const resolvedResult = await resolveExtMediaUrl(site, rawUrl, { ep: '1' });
                    rawUrl = resolvedResult.url;
                }
            }
        }
    } catch (e) {
        console.error('[Ext HLS Proxy Dynamic Resolve Error]:', e.message);
    }

    const upstreamUrl = new URL(rawUrl).toString();
    const parsedUpstream = new URL(upstreamUrl);
    const isManifest = parsedUpstream.pathname.toLowerCase().includes('.m3u8');

    if (isManifest) {
        const cachedManifest = getCachedExtManifestCold(upstreamUrl);
        if (cachedManifest) {
            res.set('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
            res.set('Cache-Control', 'public, max-age=60, stale-while-revalidate=120');
            res.set('X-Ext-Cache', 'HIT');
            return res.send(cachedManifest);
        }
    }
    
    let dynamicReferer = parsedUpstream.origin + '/';
    if (parsedUpstream.hostname.includes('eanfog.cn') || parsedUpstream.hostname.includes('nkgjoa.cn') || parsedUpstream.hostname.includes('huangguo')) {
        dynamicReferer = 'https://huangguoai.com/';
    }

    const headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36',
        'Referer': dynamicReferer,
        'Origin': parsedUpstream.origin,
        'Accept': '*/*',
        'Accept-Encoding': 'identity'
    };
    if (req.headers.range) headers.Range = req.headers.range;

    try {
        let response;
        try {
            response = await axios.get(upstreamUrl, {
                timeout: 3500,
                responseType: isManifest ? 'text' : 'stream',
                headers,
                proxy: false,
                httpAgent: extMediaHttpAgent,
                httpsAgent: extMediaHttpsAgent,
                maxRedirects: 3,
                validateStatus: status => status >= 200 && status < 400
            });
        } catch (directErr) {
            // 直连失败或超时，无缝回退到 mihomo TLS 隧道代理中转
            const proxyHost = isInsideDocker ? 'mihomo' : '127.0.0.1';
            response = await axios.get(upstreamUrl, {
                timeout: 15000,
                responseType: isManifest ? 'text' : 'stream',
                headers,
                proxy: {
                    protocol: 'http',
                    host: proxyHost,
                    port: 7890
                },
                maxRedirects: 3,
                validateStatus: status => status >= 200 && status < 400
            });
        }

        if (isManifest || (typeof response.data === 'string' && response.data.includes('#EXTM3U'))) {
            const rewritten = rewriteExtHlsManifest(response.data, upstreamUrl);
            setCachedExtManifest(upstreamUrl, rewritten);
            res.set('Content-Type', 'application/vnd.apple.mpegurl; charset=utf-8');
            res.set('Cache-Control', 'public, max-age=60, stale-while-revalidate=120');
            res.set('X-Ext-Cache', 'MISS');
            return res.send(rewritten);
        }

        if (typeof response.data === 'string' && (response.data.includes('<html') || response.data.includes('<!DOCTYPE'))) {
            console.error('[Ext HLS Proxy] Received HTML instead of media stream for:', upstreamUrl);
            return res.status(502).json({ error: 'Upstream returned HTML instead of media stream' });
        }

        res.status(response.status);
        const passthroughHeaders = ['content-type', 'content-length', 'content-range', 'accept-ranges', 'cache-control'];
        for (const key of passthroughHeaders) {
            if (response.headers[key]) res.set(key, response.headers[key]);
        }
        res.set('Access-Control-Allow-Origin', '*');
        if (!response.headers['cache-control']) {
            res.set('Cache-Control', 'public, max-age=86400, immutable');
        }
        response.data.on('error', err => {
            console.error('[Ext HLS Proxy Stream Error]:', err.message);
            if (!res.headersSent) res.status(502).end();
            else res.end();
        });
        // 仅客户端真正中断时销毁上游；req.close 在请求体读取完也可能触发，不能用它判断断连
        res.on('close', () => {
            if (!res.writableEnded && !response.data.destroyed) response.data.destroy();
        });
        response.data.pipe(res);
    } catch (err) {
        console.error(`[Ext HLS Proxy] ${upstreamUrl.substring(0, 100)}:`, err.message);
        if (!res.headersSent) res.status(502).json({ error: 'HLS proxy failed' });
    }
});

// 网页前端错误上报（诊断黑屏用，上线后可移除）
app.post('/api/debug-report', express.json(), (req, res) => {
    const tag = String(req.body && req.body.tag || 'log');
    const msg = String(req.body && req.body.msg || '');
    const line = `[WEB-DEBUG ${tag}] ${new Date().toISOString()} ${msg.slice(0, 900)}`;
    console.log(line);
    try { fs.appendFileSync('/app/debug.log', line + '\n'); } catch (e) { }
    res.json({ ok: true });
});

// 扩展源卡片/推荐/专区 API（支持 huangguo 等 type:3 csp 扩展源首页卡片）
app.get('/api/ext/cards', async (req, res) => {
    const siteKey = req.query.site_key || 'huangguo';
    const tab = req.query.tab || 'home';
    const page = parseInt(req.query.page, 10) || 1;
    const nocache = req.query.nocache === '1';

    const sites = getDB().sites;
    const site = sites.find(s => s.key === siteKey);
    if (!site || !isExtSite(site)) {
        return res.status(404).json({ error: 'Ext site not found', results: [] });
    }

    const cacheKey = `ext_cards_${siteKey}_${tab}_${page}`;
    if (!nocache) {
        const cached = cacheManager.get('detail', cacheKey);
        if (cached) {
            return res.json(cached);
        }
    }

    try {
        const loadCardItems = async (routeMode = '') => {
            let items = [];
            const runOpts = routeMode ? { routeMode } : {};
            if (siteKey === 'huangguo' && (tab === 'home' || tab === 'all')) {
                if (page === 1) {
                    const [rankR, homeR] = await Promise.allSettled([
                        runExtJs(site, 'getCards', { id: 'ranks/hot', page: 1 }, runOpts),
                        runExtJs(site, 'getCards', { id: 'home', page: 1 }, runOpts)
                    ]);
                    const seen = new Set();
                    for (const r of [rankR, homeR]) {
                        if (r.status === 'fulfilled' && r.value && Array.isArray(r.value.list)) {
                            for (const item of r.value.list) {
                                const id = String(item.vod_id || item.ext?.id || '');
                                if (id && !seen.has(id)) { seen.add(id); items.push(item); }
                            }
                        }
                    }
                } else {
                    const r = await runExtJs(site, 'getCards', { id: 'ai-duanju', page }, runOpts).catch(() => null);
                    if (r && Array.isArray(r.list)) items = r.list;
                }
            } else {
                let tabArg = { id: tab, page };
                if (tab === 'home') {
                    const cfg = await runExtJs(site, 'getConfig', {}, runOpts).catch(() => null);
                    if (cfg && cfg.tabs && cfg.tabs.length) {
                        const nonFilter = cfg.tabs.find(t => !t.ext || t.ext.type !== 'filter') || cfg.tabs[0];
                        tabArg = { ...(nonFilter.ext || { id: nonFilter.id || 'home' }), page };
                    }
                }
                const r = await runExtJs(site, 'getCards', tabArg, runOpts);
                if (r && Array.isArray(r.list)) items = r.list;
            }
            return items;
        };

        let rawItems = await loadCardItems();
        // 某些站点会以 HTTP 200 返回空页：自动强制切换网络路径再试。
        // 默认路径为空时先走代理，再走纯直连，兼容地区限制与“代理反而被拦截”两类源。
        let routeUsed = 'auto';
        if (rawItems.length === 0 && siteKey !== 'huangguo') {
            for (const routeMode of ['proxy', 'direct']) {
                try {
                    const retried = await loadCardItems(routeMode);
                    if (retried.length > 0) {
                        rawItems = retried;
                        routeUsed = routeMode;
                        console.log(`[Ext Cards] ${site.name} auto empty, recovered via ${routeMode}: ${retried.length}`);
                        break;
                    }
                } catch (e) {
                    console.warn(`[Ext Cards] ${site.name} ${routeMode} retry failed: ${e.message}`);
                }
            }
        }

        const results = rawItems.map(item => mapExtCard(item, siteKey, site.name));

        // 📄 动态分页深度：不再写死 5 页。EXT 短剧源(黄果/河马等)实际能翻几十上百页，
        //    按源+tab 给真实上限(深源可翻更多)，浅源翻到空页前端自然截断。
        //    前端 fetchRow 以"results 为空"兜底停更，此处给上限避免死循环请求空页。
        let totalPages = 5; // 默认兜底
        const DEEP_PAGE_TABS = ['ai-duanju', 'ranks/hot', 'all']; // 可深翻的分类
        if (siteKey === 'huangguo') {
            totalPages = DEEP_PAGE_TABS.includes(tab) ? 60 : 10;   // 黄果分类/榜单可翻 60 页
        } else {
            // 其它 EXT 源保守给 10 页(多数只支持有限页)，翻空自动停
            totalPages = 10;
        }

        const data = { results, total_pages: totalPages, page, route: routeUsed };
        if (results.length > 0) {
            cacheManager.set('detail', cacheKey, data, 300); // 推荐列表缓存 5 分钟，兼顾实时更新与加载速度
            recordSiteHealth(siteKey, true);
        } else {
            recordSiteHealth(siteKey, false);
        }

        // 🚀 首页主卡后台并行预热：前 6 部同时缓存首集媒体直链，其余只缓存结构。
        if (results.length > 0) {
            setImmediate(() => Promise.allSettled(results.slice(0, 10).map(async (item, index) => {
                const vid = item.vod_id;
                const tracksKey = `ext_tracks_${siteKey}_${vid}`;
                let tr = cacheManager.get('detail', tracksKey);
                if (!tr) {
                    let trackUrl;
                    if (siteKey === 'age') trackUrl = `https://api.agedm.io/v2/detail/${vid}`;
                    else if (siteKey === 'kuaikaw') trackUrl = `https://www.kuaikaw.cn/drama/${vid}`;
                    else if (siteKey === 'ppnix') trackUrl = `https://www.ppnix.com/cn/movie/${vid}.html`;
                    tr = await runExtJs(site, 'getTracks', { id: vid, url: trackUrl });
                    if (tr && (tr.list || tr.tracks)) cacheManager.set('detail', tracksKey, tr, 1800);
                }
                if (index < 6 && tr) {
                    const groups = tr.list || (tr.tracks ? [tr] : []);
                    const firstTrack = groups[0]?.tracks?.[0] || groups[0]?.list?.[0];
                    let firstUrl = firstTrack?.ext?.url || firstTrack?.url || '';
                    if (firstUrl && !/\.(?:m3u8|mp4)(?:[?#]|$)/i.test(firstUrl)) {
                        try {
                            const r = await resolveExtMediaUrl(site, firstUrl, firstTrack.ext || { ep: '1' });
                            if (r && r.url) firstUrl = r.url;
                        } catch (e) { }
                    }
                    // 首页卡片预热顺带把首集 m3u8 清单缓存上，用户点开即播（封面加载后通常已有 1-2s 缓冲）。
                    warmExtManifest(siteKey, firstUrl);
                }
            })));
        }

        res.json(data);
    } catch (err) {
        recordSiteHealth(siteKey, false);
        console.error(`[Ext Cards Error] ${site.name}:`, err.message);
        res.status(500).json({ error: 'Failed to fetch cards', results: [] });
    }
});

// ========== P3 站点健康度（首页自适应排序） ==========
// 内存级轻量统计：记录每次 getCards 成功/失败，首页聚合按健康分排序，
// 慢源/故障源自动后置，健康/热门前置。带时间衰减 + 封顶防无限增长。
const siteHealth = new Map(); // key → { ok, total, lastOk, lastFail, updatedAt }
function recordSiteHealth(siteKey, ok) {
    try {
        const k = String(siteKey || '').toLowerCase();
        if (!k) return;
        const h = siteHealth.get(k) || { ok: 0, total: 0, lastOk: 0, lastFail: 0, updatedAt: 0 };
        h.total++;
        if (ok) {
            h.ok++;
            h.lastOk = Date.now();
            const dropRatio = h.total > 40 ? 0.9 : 1; // 长期衰减旧样本，保持对近期波动的敏感
            h.ok = Math.round(h.ok * dropRatio);
            h.total = Math.round(h.total * dropRatio);
        } else {
            h.lastFail = Date.now();
        }
        h.updatedAt = Date.now();
        siteHealth.set(k, h);
        if (siteHealth.size > 200) {
            const oldest = [...siteHealth.entries()].sort((a, b) => a[1].updatedAt - b[1].updatedAt)[0];
            if (oldest) siteHealth.delete(oldest[0]);
        }
    } catch (e) { }
}
function siteHealthScore(siteKey) {
    const h = siteHealth.get(String(siteKey || '').toLowerCase());
    if (!h || !h.total) return 50;
    const base = (h.ok / h.total) * 100;
    const recentPenalty = h.lastFail > h.lastOk ? 15 : 0;
    return Math.max(0, base - recentPenalty);
}
function siteHealthRows(rows) {
    // rows: [{key, results}] ；EXT 行按来源站点健康度排序，健康者在前；非 EXT 行保底排最前。
    return [...rows].sort((a, b) => {
        const ta = HOME_EXT_TARGETS[a.key];
        const tb = HOME_EXT_TARGETS[b.key];
        if (!tb) return -1;
        if (!ta) return 1;
        return siteHealthScore(tb[0]) - siteHealthScore(ta[0]);
    });
}

// 🏷 EXT 卡片统一映射：透传上游类型/年份/真实评分，并从 remarks 解析出可筛选的
//    类型标签(genre) 与评分。首页聚合 /api/ext/cards 与 /api/home 共用，字段一致。
function mapExtCard(item, siteKey, siteName) {
    const id = String(item.vod_id || item.id || item.ext?.id || '');
    const name = item.vod_name || item.name || item.title || '';
    const remarks = String(item.vod_remarks || item.remarks || item.subTitle || '').replace(/<[^>]+>/g, '').trim();
    let score = 8.8;
    const upScore = parseFloat(item.vod_score) || parseFloat(item.score);
    if (upScore) score = upScore;
    else { const sm = remarks.match(/([\d\.]+)分/); if (sm) score = parseFloat(sm[1]); }
    score = Math.min(10, Math.max(0, score));
    let typeName = item.type_name || item.category || item.class_name || '';
    const yearRaw = item.vod_year || item.year || '';
    const genre = [];
    // 📺 更新至第几集（"更新至03集"/"18小时前更新至1集"里挖出来，可做筛选维度）
    let updateEp = '';
    try {
        const upm = remarks.match(/(?:更新至|更新到|更至)?\s*(\d{1,4})集/);
        if (upm) updateEp = upm[1];
        for (const t of remarks.split('·').map(s => s.trim()).filter(Boolean)) {
            if (/^[\d.]+分$/.test(t)) continue;                         // "9.4分"
            if (/^[\d.,万]+集?$/.test(t)) continue;                     // "187集" "7.85万"
            if (/^更新至?\d+集$/i.test(t)) continue;                    // "更新至03集"
            if (/^第\d+集$/i.test(t)) continue;                         // "第04集"
            if (/^(?:刚刚|[\d.]+(?:小时|天|分钟|分|秒))前.*(?:更新|至)?/i.test(t)) continue; // "18小时前更新至1集"
            if (t === '正片' || t === '精选' || t === '全集' || t === '全') continue;
            if (!genre.includes(t)) genre.push(t);
        }
    } catch (e) { }
    if (!typeName && genre.length) typeName = genre[0];
    return {
        id: `ext_${siteKey}_${id}`, vod_id: id, title: name, name: name,
        original_title: '', original_name: '',
        poster_path: item.vod_pic || item.pic || item.cover || item.poster || '',
        detail_url: item.ext?.url || item.ext?.play_url || '',
        vote_average: score, score, genre, type_name: typeName, year: yearRaw || '', updateEp,
        release_date: remarks || '精选', first_air_date: remarks || '精选', remarks,
        site_key: siteKey, site_name: siteName
    };
}

// ========== 🔥 搜索热词 TTL ==========
// 统计每个搜索词在滚动窗口内的请求热度。热门词(≥3 次)的搜索缓存 TTL 翻倍：
// 反正反复有人搜,缓存保持更久命中率更高、源站压力更小；冷门词照常 1h 过期不占空间。
// 注：仅按"词频"计热，与站点无关(热词全域通用)。
const searchTermHits = new Map(); // 词(归一化小写) → 最近 hits 数
function recordSearchTerm(rawKw) {
    try {
        const k = String(rawKw || '').trim().toLowerCase().slice(0, 40);
        if (!k) return;
        const cur = (searchTermHits.get(k) || 0) + 1;
        searchTermHits.set(k, cur);
        // 🔥 刚跨过热词门槛(≥3) → 立即把该词所有站点的 search 缓存 TTL 延长到 7200s。
        //    否则热词第3次请求若命中缓存就不会重新 set, TTL 永远停在首次的 3600s。
        if (cur === 3 && cacheManager && cacheManager.type === 'sqlite' && cacheManager.db) {
            try {
                const like = `%${k}`;  // cacheKey 形如 <site>_<word>
                const res = cacheManager.db.prepare(
                    'UPDATE cache SET expire = ? WHERE category = ? AND key LIKE ? AND expire < ?'
                ).run(Date.now() + 7200 * 1000, 'search', like, Date.now() + 3600 * 1000);
                if (res.changes > 0) {
                    console.log(`[热词] '${k}' 成为热词, ${res.changes} 条搜索缓存 TTL 翻倍至 2h`);
                }
            } catch (e) { }
        }
        if (searchTermHits.size > 500) {  // 只保留最活跃的词，防 Map 无限涨
            const oldest = [...searchTermHits.entries()].sort((a, b) => a[1] - b[1])[0];
            if (oldest) searchTermHits.delete(oldest[0]);
        }
        return cur;
    } catch (e) { return 0; }
}
// 返回该词的 search 缓存 TTL：热词翻倍(7200s)，冷门 3600s
function searchTTL(keyword) {
    const k = String(keyword || '').trim().toLowerCase().slice(0, 40);
    const hits = searchTermHits.get(k) || 0;
    return hits >= 3 ? 7200 : 3600;
}

// ========== P0-1 首页聚合接口 /api/home ==========
// 一次并行返回 hero + 前 N 行榜单，把首页打开从 N 次串行请求降为 1 次。
// 前端渐进式使用：拿到即填充首屏(其余行仍按原逐行补拉)；接口失败/超时前端自动回退逐行。
// 单行失败只把该行留空，不影响其它行；整包 90s 缓存分担多用户并发。
const HOME_ROW_KEYS = [
    'huangguoRow', 'kuaikawRow', 'ageRow', 'ppnixRow', 'bde4Row', 'zxzjRow',
    'libvioRow', 'aiRow', 'dubokuRow'
];
// EXT 行 → (site_key, tab)
const HOME_EXT_TARGETS = {
    huangguoRow: ['huangguo', 'home'], kuaikawRow: ['kuaikaw', 'home'], ageRow: ['age', 'home'],
    ppnixRow: ['ppnix', 'home'], bde4Row: ['bde4', 'home'], zxzjRow: ['Zxzj', 'home'],
    libvioRow: ['libvio', 'home'], aiRow: ['ai', 'home'], dubokuRow: ['duboku', 'home']
};

async function homeFetchTmdb(path, page = 1) {
    const TMDB_API_KEY = process.env.TMDB_API_KEY;
    if (!TMDB_API_KEY) return null;
    const cacheKey = `tmdb_proxy_${path}_${page}`;
    const cached = cacheManager.get('detail', cacheKey);
    if (cached) return cached;
    try {
        const finalUrl = `https://api.themoviedb.org/3${path}`;
        const response = await axios.get(finalUrl, {
            params: { page, api_key: TMDB_API_KEY, language: 'zh-CN' },
            timeout: 12000
        });
        cacheManager.set('detail', cacheKey, response.data, 3600);
        return response.data;
    } catch (e) {
        console.warn(`[Home] TMDB fetch failed ${path}:`, e.message);
        return null;
    }
}

async function homeGetExtCards(siteKey, tab, timeoutMs = 8000) {
    const sites = getDB().sites;
    const site = sites.find(s => s.key === siteKey && isExtSite(s));
    if (!site) return [];
    const cacheKey = `ext_cards_${siteKey}_${tab}_1`;
    const cached = cacheManager.get('detail', cacheKey);
    if (cached && Array.isArray(cached.results)) {
        return cached.results.slice(0, 10);
    }
    try {
        const loadCards = async (routeMode = '') => {
            const runOpts = routeMode ? { routeMode } : {};
            let tabArg = { id: tab, page: 1 };
            if (tab === 'home') {
                const cfg = await runExtJs(site, 'getConfig', {}, runOpts).catch(() => null);
                if (cfg && cfg.tabs && cfg.tabs.length) {
                    const nonFilter = cfg.tabs.find(t => !t.ext || t.ext.type !== 'filter') || cfg.tabs[0];
                    tabArg = { ...(nonFilter.ext || { id: nonFilter.id || 'home' }), page: 1 };
                }
            }
            const r = await runExtJs(site, 'getCards', tabArg, runOpts);
            return r && Array.isArray(r.list) ? r.list : [];
        };
        // 🏷 卡片映射统一走顶层 mapExtCard（透传类型/年份/真实评分 + 解析 genre 标签）
        // 每源独立截止：单行慢/坏源不拖累整个首页聚合
        const withTimeout = (p, ms = timeoutMs) => Promise.race([
            p,
            new Promise((_, rej) => setTimeout(() => rej(new Error('home-timeout')), ms))
        ]);
        let items = await withTimeout(loadCards());
        // 与 /api/ext/cards 相同：HTTP200空页时先走代理、再走纯直连，兼容两类地区限制源
        if (items.length === 0 && siteKey !== 'huangguo') {
            for (const routeMode of ['proxy', 'direct']) {
                try {
                    const retried = await withTimeout(loadCards(routeMode), Math.min(6000, timeoutMs));
                    if (retried.length > 0) {
                        items = retried;
                        console.log(`[HOME] ${site.name} auto empty, recovered via ${routeMode}: ${retried.length}`);
                        break;
                    }
                } catch (e) {
                    console.warn(`[HOME] ${site.name} ${routeMode} retry failed: ${e.message}`);
                }
            }
        }

        if (items.length > 0) {
            recordSiteHealth(siteKey, true);
            const results = items.map(item => mapExtCard(item, siteKey, site.name));
            // 首页聚合同样按源给真实深度(黄果可深翻)，浅源兜底；前端 fetchRow 空页自动停
            const hp = siteKey === 'huangguo' ? 60 : 10;
            const data = { results, total_pages: hp, page: 1, route: 'auto' };
            if (results.length > 0) cacheManager.set('detail', `ext_cards_${siteKey}_${tab}_1`, data, 300);
            return results.slice(0, 10);
        }
        recordSiteHealth(siteKey, false);
        return [];
    } catch (e) {
        recordSiteHealth(siteKey, false);
        console.warn(`[HOME] ext cards failed ${siteKey}/${tab}:`, e.message);
        return [];
    }
}

// /api/home：内存快照 + stale-while-revalidate，绝不让用户等坏源超时。
// 每次请求：新鲜(<90s)直接返回；过期则先返回旧快照，后台异步重建（只重建未缓存行）。
let homeSnapshot = null;      // { hero, rows, updatedAt }
let homeSnapshotBuilding = false; // 重建中防并发
let warmupPromise = null;     // P0-3 启动预热 promise（route 首次构建等待它完成，避免与 warmup 重复拉源）
const HOME_SNAPSHOT_TTL = 90000;
const HOME_CARD_TTL = 300;   // ext_cards 单行缓存 5 分钟，重建成行秒回

async function buildHomeSnapshot() {
    const keys = HOME_ROW_KEYS;
    const [heroData, ...rowDatas] = await Promise.all([
        homeFetchTmdb('/trending/all/week', 1),
        ...keys.map(k => {
            const t = HOME_EXT_TARGETS[k];
            return homeGetExtCards(t ? t[0] : 'huangguo', t ? t[1] : 'home');
        })
    ]);
    const hero = (heroData && Array.isArray(heroData.results))
        ? heroData.results.filter(i => i.backdrop_path).slice(0, 5).map(item => ({
            title: item.title || item.name,
            originalTitle: item.original_title || item.original_name || '',
            overview: item.overview || '精彩内容不容错过',
            backdrop: item.backdrop_path,
            poster: item.poster_path || '',
            rawData: item
        }))
        : [];
    const rows = keys.map((key, idx) => ({
        key,
        results: (rowDatas[idx] || []).slice(0, 10)
    }));
    return { hero, rows: siteHealthRows(rows), sorted: true, updatedAt: Date.now() };
}

app.get('/api/home', async (req, res) => {
    try {
        const now = Date.now();
        const fresh = homeSnapshot && (now - homeSnapshot.updatedAt < HOME_SNAPSHOT_TTL);
        if (fresh) return res.json(homeSnapshot);

        // 有过期快照：立即返回旧数据，后台重建（stale-while-revalidate）
        if (homeSnapshot) {
            const stale = homeSnapshot;
            if (!homeSnapshotBuilding) {
                homeSnapshotBuilding = true;
                setImmediate(() => {
                    buildHomeSnapshot().then(snap => {
                        if (snap && snap.rows.length) { homeSnapshot = snap; }
                    }).catch(e => console.warn('[HOME] 后台重建失败:', e.message))
                    .finally(() => { homeSnapshotBuilding = false; });
                });
            }
            return res.json(stale);
        }

        // 无快照：首次构建（首个用户等待，坏源 8s 封顶；若 warmup 正在跑则等它完成复用缓存）
        homeSnapshotBuilding = true;
        try {
            if (warmupPromise) {
                try { await warmupPromise; } catch (e) { }
            }
            const snap = await buildHomeSnapshot();
            if (snap && snap.rows.length) homeSnapshot = snap;
            res.json(homeSnapshot || { hero: [], rows: [], sorted: true });
        } finally {
            homeSnapshotBuilding = false;
        }
    } catch (err) {
        console.error('[HOME] Aggregate error:', err.message);
        res.status(502).json({ error: 'Home aggregate failed', hero: [], rows: [] });
    }
});

// ========== P0-3 启动预热：重启后立即并行预热首页各源结构+首卡，配合磁盘缓存“重启不冷” ==========
async function startupWarmup() {
    // 预热 promise 存全局：route 首次构建等待它，避免重复拉源
    warmupPromise = (async () => {
        try {
            console.log('[P0-3] 启动预热开始 (HOME rows 前台 + 扩展源后台)...');
            const keys = Object.keys(HOME_EXT_TARGETS);
            // 3s 短超时预热：快源先缓存，坏源不阻塞（3s 后放弃留给 route 实时拉）
            await Promise.allSettled(keys.map(async (k) => {
                const [siteKey, tab] = HOME_EXT_TARGETS[k];
                try { await homeGetExtCards(siteKey, tab, 3000); } catch (e) { }
            }));
            // 构建聚合快照：此时各行大多已命中 ext_cards 缓存，秒回
            try {
                const snap = await buildHomeSnapshot();
                if (snap && snap.rows.length) homeSnapshot = snap;
                console.log(`[P0-3] 启动预热完成 (${snap.rows.length} 行)`);
            } catch (e) {
                console.warn('[P0-3] Aggregate warmup skipped:', e.message);
            }
        } catch (e) {
            console.warn('[P0-3] 启动预热异常:', e.message);
        }
    })();
    try { await warmupPromise; } catch (e) { }
}

// 1. 获取站点列表
app.get('/api/sites', async (req, res) => {
    // 尝试从远程加载
    let sitesData = REMOTE_DB_URL ? await loadRemoteDb() : null;

    // 回退到本地
    if (!sitesData) {
        sitesData = JSON.parse(fs.readFileSync(DATA_FILE));
    }

    res.json(withSiteProfiles(sitesData));
});

// 服务器端测速兜底：客户端直连+代理都失败时(混合内容/CORS)由服务器测资源站 API 延迟。
// 注：此接口在早期重构中丢失，前端一直调用导致 404 → 服务器测速这条兜底失效，已恢复。
// 🗄️ 内存缓存 + 同站并发合并:海外用户每开一部剧,所有"海外受限"站都会走到这里(实测每次 p50 245ms、最慢 1.6s,
//    且每次 1-2 个上游请求)。通的缓存 5 分钟、不通的 90 秒;上游【超时】得出的 9999 带 transient:true 且不缓存
//    ——前端据此不写 12h 死亡缓存(超时是瞬态,不能把站封半天)。只用内存(不进 detail 缓存:json 模式每写一次整文件重写)。
const checkCache = new Map();      // key -> { data, expiry }
const checkInflight = new Map();   // key -> Promise<data>
const CHECK_OK_TTL = 5 * 60 * 1000, CHECK_FAIL_TTL = 90 * 1000, CHECK_CACHE_MAX = 1000;
const isTimeoutErr = (e) => !!e && (e.code === 'ECONNABORTED' || e.code === 'ETIMEDOUT' || /timeout/i.test(String(e.message || '')));
app.get('/api/check', async (req, res) => {
    const key = String(req.query.key || '');
    // 「刷新线路」带 nocache=1:跳过读缓存强制真测(结果照样写回、照样并发合并)
    const hit = req.query.nocache === '1' ? null : checkCache.get(key);
    // 缓存里的失败只当【瞬态】发给别的用户:一次上游抖动(502/连接重置)不能经 90s 缓存扩散成每个人本地 12h 的死亡记录;
    //   只有亲自跑了这次探测的那个请求拿到非 transient 的失败
    if (hit && hit.expiry > Date.now()) return res.json(hit.data.latency >= 9000 ? Object.assign({}, hit.data, { transient: true }) : hit.data);
    let p = checkInflight.get(key);
    const mine = !p;   // 这次请求亲自跑探测;并发合并进来的请求拿到失败时一律按瞬态(同缓存命中的规则)
    if (!p) {
        p = runSiteCheck(key).then((data) => {
            if (!data.transient) {
                if (checkCache.size >= CHECK_CACHE_MAX) checkCache.delete(checkCache.keys().next().value);
                checkCache.set(key, { data, expiry: Date.now() + (data.latency < 9000 ? CHECK_OK_TTL : CHECK_FAIL_TTL) });
            }
            return data;
        }).catch(() => ({ latency: 9999, transient: true })).finally(() => checkInflight.delete(key));
        checkInflight.set(key, p);
    }
    const d = await p;
    res.json(!mine && d.latency >= 9000 && !d.transient ? Object.assign({}, d, { transient: true }) : d);
});
async function runSiteCheck(key) {
    try {
        const sites = allSites();
        const site = sites.find(s => s.key === key);
        // 🎌 规则站没有 maccms API:只测站点首页可达(绝不拉媒体,同下方铁律)
        if (site && kazumi && kazumi.isKzSite(site)) return await kazumi.check(site.key);
        if (!site || !site.api) return { latency: 9999 };
        const start = Date.now();
        try {
            // 必须返回【有效 videolist JSON 且有 http 播放地址】才算通——挡掉返回 200 的死站
            // (域名停放页/Cloudflare 人机校验页/HTML 报错页,它们解析不出 JSON list → 9999)。
            // ⚠️ 但【绝不在服务器上真拉 m3u8 验证】:VPS 是数据中心 IP,视频 CDN 普遍封机房出口(这正是要建
            //    CORS worker 的原因)——曾加过"抽样 m3u8 拉一次验 #EXTM3U",结果生产上【所有站】全判 9999
            //    (可用性检查形同虚设,前端超时死锁下全站不可播,事故)。且抽样的是榜单第一页随机片,住宅网络实测
            //    健康站也常抽到 403/404 过期链接。真实可播性只能由【客户端】直连/代理测速把关,服务器只管
            //    "API 活着且返回正经片库"这一层。
            const UA_HDRS = { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36', 'Accept': 'application/json' };
            let list = null, timedOut = false;
            try {
                const r = await axios.get(`${site.api}?ac=videolist&pg=1`, { timeout: 4000, responseType: 'json', headers: UA_HDRS });
                list = r.data && Array.isArray(r.data.list) ? r.data.list : null;
            } catch (e) { timedOut = isTimeoutErr(e); }
            if (!list || !list.length) {
                // 部分 CMS 变体对 ac=videolist 返回空/不支持 → 退回 ac=detail 再试一次(资源站验活的既定铁律)
                try {
                    const r2 = await axios.get(`${site.api}?ac=detail&pg=1`, { timeout: 4000, responseType: 'json', headers: UA_HDRS });
                    list = r2.data && Array.isArray(r2.data.list) ? r2.data.list : null;
                    timedOut = false;
                } catch (e) { timedOut = timedOut || isTimeoutErr(e); }
            }
            if (!list || !list.length) return timedOut ? { latency: 9999, transient: true } : { latency: 9999 };
            if (!list.some(v => /https?:\/\//.test(String(v.vod_play_url || '')))) return { latency: 9999 };
            return { latency: Date.now() - start, _testType: 'server' };
        } catch (e) {
            return isTimeoutErr(e) ? { latency: 9999, transient: true } : { latency: 9999 };
        }
    } catch (e) {
        return { latency: 9999, transient: true };
    }
}

// 🔗 分享深链预览：未登录用户打开 /?play=剧名 时，前端用本接口拿 TMDB 简介+海报渲染"锁定框架"
//   （标题+简介+黑屏播放器+登录提示），全程不碰任何资源站(不搜索/不取播放地址)。带内存缓存+限流防刷。
const previewCache = new Map(); // name -> { data, expiry }
const PREVIEW_CACHE_TTL = 6 * 60 * 60 * 1000;   // 命中(有简介/海报)缓存 6 小时
const PREVIEW_MISS_TTL = 10 * 60 * 1000;        // 未命中(降级)缓存 10 分钟，便于稍后重试
const PREVIEW_CACHE_MAX = 2000;                  // FIFO 容量上限，防止无限增长
// 全站 TMDB 调用封顶：即使有人伪造 X-Forwarded-For 绕过单 IP 限流 + 用不同 name 绕过缓存，
// 也无法把 /api/preview 变成无限的 TMDB 放大器(超额则只返回降级的"仅剧名"数据)。
let previewTmdbWindowStart = 0, previewTmdbCount = 0;
const PREVIEW_TMDB_WINDOW = 60 * 1000;
const PREVIEW_TMDB_MAX = 300;                     // 全站每分钟最多 300 次 TMDB 查询
function previewTmdbBudgetOk() {
    const now = Date.now();
    if (now - previewTmdbWindowStart > PREVIEW_TMDB_WINDOW) { previewTmdbWindowStart = now; previewTmdbCount = 0; }
    if (previewTmdbCount >= PREVIEW_TMDB_MAX) return false;
    previewTmdbCount++;
    return true;
}
app.get('/api/preview', async (req, res) => {
    const name = String(req.query.name || '').slice(0, 100).trim();
    if (!name) return res.json({ name: '', title: '', synopsis: '', poster: '', year: '' });

    const cached = previewCache.get(name);
    if (cached && cached.expiry > Date.now()) {
        res.set('Cache-Control', 'public, max-age=3600');
        return res.json(cached.data);
    }

    const data = { name, title: name, synopsis: '', poster: '', year: '' };
    try {
        const TMDB_API_KEY = process.env.TMDB_API_KEY;
        if (TMDB_API_KEY && previewTmdbBudgetOk()) {
            const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];
            const serverInChina = process.env['SERVER_IN_CHINA'] === 'true';
            const base = (TMDB_PROXY_URL && serverInChina) ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3` : 'https://api.themoviedb.org/3';
            const r = await axios.get(`${base}/search/multi`, { params: { api_key: TMDB_API_KEY, language: 'zh-CN', query: name }, timeout: 2500 });
            const results = (r.data && r.data.results) || [];
            // 优先选既有海报又有简介的，其次有海报的，最后第一个
            const hit = results.find(x => (x.poster_path || x.backdrop_path) && x.overview)
                || results.find(x => x.poster_path || x.backdrop_path)
                || results[0];
            if (hit) {
                data.title = hit.title || hit.name || name;
                data.synopsis = hit.overview || '';
                if (hit.poster_path || hit.backdrop_path) data.poster = `https://image.tmdb.org/t/p/w500${hit.poster_path || hit.backdrop_path}`;
                const d = hit.release_date || hit.first_air_date || '';
                data.year = d ? String(d).slice(0, 4) : '';
            }
        }
    } catch (e) { /* 忽略，返回降级数据(仅剧名) */ }

    // 写缓存(含降级结果，FIFO 容量上限)；命中与未命中用不同 TTL
    if (previewCache.size >= PREVIEW_CACHE_MAX) {
        const firstKey = previewCache.keys().next().value;
        if (firstKey !== undefined) previewCache.delete(firstKey);
    }
    const ttl = (data.synopsis || data.poster) ? PREVIEW_CACHE_TTL : PREVIEW_MISS_TTL;
    previewCache.set(name, { data, expiry: Date.now() + ttl });

    res.set('Cache-Control', 'public, max-age=3600');
    return res.json(data);
});

// 🗨️ 弹幕代理：把"剧名+集名"映射到自建第三方弹幕聚合服务(danmu_api，兼容弹弹play，聚合爱优腾芒B等平台弹幕)，
//   再转成 DPlayer v3 格式。按 DPlayer 约定 danmaku.api='/api/danmaku/'，它会 GET /api/danmaku/v3/?id=<剧名|集名>。
//   需配置环境变量 DANMU_API_URL(你部署的 danmu_api 地址)；未配置则返回空弹幕(功能优雅降级，不报错)。
const danmakuCache = new Map(); // "剧名|集名" -> { data, lowConf, expiry }  只放空结果/低置信结果(短期);高贴合非空结果进 danmakuStore
const danmakuSearchCache = new Map(); // norm(剧名) -> { animes, expiry } 同剧各集复用搜索结果
const danmakuAltTitle = new Map();    // 实例||norm(剧名) -> { alt, expiry } 换写法才搜得到 / { none, expiry } 换写法也搜不到
const danmakuUrlMode = new Map();    // danmu_api 实例 -> 发现它不认 comment?url=(老版本,只能按 id)的时间
const DANMAKU_MISS_TTL = 90 * 1000; // 空结果只缓存 90s：弹幕空多为 danmu_api 被上游(iqiyi)限流的瞬时失败，短缓存让下次很快重试成功(成功后再长缓存)
const DANMAKU_LOWCONF_TTL = 10 * 60 * 1000;
// ⏳ 弹幕端点前台最多等多久(到点回 pending,见 /api/danmaku/v3/);后台抓取不受它限制。DANMAKU_FG_WAIT_MS 只是给回归测试调小用的
const DANMAKU_FG_WAIT = Number(process.env.DANMAKU_FG_WAIT_MS) > 0 ? Number(process.env.DANMAKU_FG_WAIT_MS) : 45000;
const DANMAKU_CACHE_MAX = 1000;
// 🗄️ 高贴合非空弹幕的服务器长缓存(见 lib/danmaku-store):SQLite 持久(gzip)+ 内存热层,7 天新鲜、过期先回旧的再后台重抓,
//    同一集并发只打一次 danmu_api。热剧大家都在看的那几集,一周最多回源一次,重启也不丢。
//    DANMAKU_STORE_VER:改了弹幕匹配逻辑(哪集配哪份弹幕)就 bump,旧的持久结果整体作废。
const DANMAKU_STORE_VER = 'm1';
const danmakuStore = require('./lib/danmaku-store').createStore({
    db: () => (cacheManager.type === 'sqlite' && cacheManager.db) ? cacheManager.db : null,
    freshMs: (Number(process.env.DANMAKU_CACHE_DAYS) > 0 ? Number(process.env.DANMAKU_CACHE_DAYS) : 7) * 86400e3,
});
const DANMAKU_MAX = 12000; // 单集弹幕上限(超出按时间均匀采样)。提到 1.2w 让峰值更密、"海量弹幕"开关效果明显；unlimited 关时 DPlayer 仍按轨道限并发渲染，不会卡
const DANMAKU_SEARCH_TTL = 3 * 60 * 1000; // danmu_api 的 episodeId 会过期(实测<10min)，搜索结果只短存，防复用过期id取到空弹幕
let danmakuWinStart = 0, danmakuWinCount = 0;
function danmakuBudgetOk() { // 全站每分钟最多 300 次上游弹幕查询，防刷
    const now = Date.now();
    if (now - danmakuWinStart > 60000) { danmakuWinStart = now; danmakuWinCount = 0; }
    if (danmakuWinCount >= 300) return false;
    danmakuWinCount++;
    return true;
}
// danmu_api 这边的配置问题(版本太旧、开着限流)在前台只表现为"没弹幕":每类每实例 10 分钟在日志里提醒一次怎么改
const danmakuWarnedAt = new Map();
function danmakuWarnOnce(key, msg) {
    if (Date.now() - (danmakuWarnedAt.get(key) || 0) < 600e3) return;
    danmakuWarnedAt.set(key, Date.now());
    console.warn(msg);
}
// danmu_api 自带按来源 IP 的取弹幕限流(RATE_LIMIT_MAX_REQUESTS,默认每分钟 3 次),本站替所有观众去取,在它看来只有一个 IP
function danmakuWarnRateLimited(base) {
    danmakuWarnOnce('429|' + base, `⚠️ [弹幕] ${base} 取弹幕返回 429 限流:多半是 danmu_api 没设 RATE_LIMIT_MAX_REQUESTS=0(它默认每个来源 IP 每分钟只放 3 次,本站替所有观众去取,在它看来只有一个 IP)。` +
        `给 danmu_api 设上这个环境变量再重启即可(Docker 要带 -e 重建容器,见 README「弹幕服务 danmu_api」)`);
}
// danmu_api v1.20.10 起搜索结果才带视频地址(url);更老的版本在多实例部署上按地址取不了、按 id 又会串剧
function danmakuWarnNoUrl(base) {
    danmakuWarnOnce('nourl|' + base, `⚠️ [弹幕] ${base} 的 danmu_api 太旧:搜索结果不带视频地址(url 字段 v1.20.10 起才有),本站按视频地址取弹幕,从这个实例一条都取不到。` +
        `请把 danmu_api 升级到最新版(自己服务器上只跑一个实例的,也可以设 DANMU_API_SINGLE_INSTANCE=1 改按 id 取)`);
}
function dandanToDplayer(comments) {
    // dandanplay: { p:"秒,模式,颜色,uid", m:"文本" } → DPlayer: [时间, 类型(0滚/1顶/2底), 颜色, 作者, 文本]
    const modeMap = { '1': 0, '6': 0, '5': 1, '4': 2 };
    const out = [];
    for (const c of (comments || [])) {
        const p = String(c.p || '').split(',');
        if (p.length < 3) continue;
        const t = parseFloat(p[0]);
        if (!isFinite(t)) continue;
        out.push([t, (modeMap[p[1]] != null ? modeMap[p[1]] : 0), parseInt(p[2], 10) || 16777215, '', String(c.m || '')]);
    }
    return out;
}
function danmakuCn2Num(t) {
    // 中文数字/阿拉伯数字 → int("一/十二/二十三/一百零五"，集数场景到几百足够)
    t = String(t || '');
    if (/^\d+$/.test(t)) return parseInt(t, 10);
    const D = { 零: 0, 一: 1, 二: 2, 两: 2, 三: 3, 四: 4, 五: 5, 六: 6, 七: 7, 八: 8, 九: 9 };
    let n = 0, cur = 0, any = false;
    for (const ch of t) {
        if (D[ch] != null) { cur = D[ch]; any = true; }
        else if (ch === '十') { n += (cur || 1) * 10; cur = 0; any = true; }
        else if (ch === '百') { n += (cur || 1) * 100; cur = 0; any = true; }
        else return null;
    }
    return any ? n + cur : null;
}
function danmakuEpNum(s) {
    // 优先取"第N集/话/期"里的 N(支持中文数字"第一集"；忽略"破事精英2第17集"里的剧名数字2)；取不到再退回第一个数字
    const str = String(s || '');
    let m = str.match(/第\s*0*(\d+)\s*[集话話期]/);
    if (m) return parseInt(m[1], 10);
    m = str.match(/第\s*([一二两三四五六七八九十百零]+)\s*[集话話期]/);
    if (m) { const n = danmakuCn2Num(m[1]); if (n != null) return n; }
    const m2 = str.match(/\d+/);
    return m2 ? parseInt(m2[0], 10) : null;
}
// 集名先剥离【同内容标签】(语言/画质/权益标注，不改变内容本体)——"第24集(会员版)"就是第24集、"第10期 中字"就是第10期，
//   拉丁标签(HD/BD/1080P/HDR…)要求【词边界】且允许连写，防误剥 BTS/HDTV/CATCH；剥后残留仅剩数字(+版/帧)且【确实剥过标签】视同全标签(电影 "BD1280高清";裸集号 02/03 不清)。
const DANMAKU_LABEL_LATIN = /(?<![A-Za-z0-9])(?:HDR|HD|BD|TC|TS|HC|UHD|SD|DVD|WEB-?DL|WEBRip|BluRay|REMUX|\d{3,4}[Pp]|[48][Kk])+(?![A-Za-z])/gi;
const DANMAKU_LABEL_CN = /(中文字幕|中字|双字|双语|国语|粤语|台配|日语|韩语|英语|无水印|完整版|会员加长版|加长版|未删减|超清|高清|蓝光|标清|修复版|导演剪辑版|杜比视界|会员版|超前点播|超前版|抢先版|点映版|点映|VIP版?)/g;
function danmakuCleanEpName(s) {
    const orig = String(s || '');
    let r = orig.replace(DANMAKU_LABEL_LATIN, '').replace(DANMAKU_LABEL_CN, '');
    if (r !== orig && !/[集话話期]/.test(r) && /^[\s·]*\d{2,4}[\s·]*(?:版|帧|周年?)?[\s·]*$/.test(r)) r = '';
    return r;
}
// 变体词(正片的不同剪辑/子场,时间轴不同 → 须精确匹配,不回落正片)；额外内容(与正片时间轴完全无关 → 只配同类)。
//   刻意【不含】会员/超前/抢先(会员版/超前点播/抢先版是标签,已由 DANMAKU_LABEL_CN 剥掉;裸"会员福利"是看点)、
//   【不含】幕后/反应(连锁反应/幕后玩家是真实片名/剧名,极易误判)——对抗审查三轮抓出的高频误伤词。
const DM_VARIANT = '纯享|加更|特辑|发布会|见面会|专场|访谈|饭局|plus';
const DM_EXTRA = '先导|预告|彩蛋|花絮|片花|直拍|reaction|repo';
const DM_VAR_RE = new RegExp('^(?:' + DM_VARIANT + ')', 'i');
const DM_EXTRA_RE = new RegExp('^(?:' + DM_EXTRA + ')', 'i');
const DM_TOK_VAR = new RegExp('^(?:' + DM_VARIANT + ')$', 'i');
// 额外内容【标签形态】：可选短前缀(独家/幕后/正片…) + 额外词 + 可选后缀(片/版/集锦…)。用于识别 "独家花絮"/"第5集独家花絮"/"预告片",
//   但不误判 "末日预告"/"连锁反应"(内容词+关键词,前缀不在白名单)。
const DM_EXTRA_LABEL = new RegExp('^(?:独家|幕后|正片|精彩|完整|删减|未播|拍摄|花絮|片花)?(?:' + DM_EXTRA + ')(?:片|版|集锦|合集|篇|特辑)?$', 'i');
const dmExtraKw = str => { const km = String(str).match(new RegExp('(?:' + DM_EXTRA + ')', 'i')); return km ? km[0].toLowerCase() : ''; };
const DM_SEP = /[\s:：,，、;；。•‧＆&|/·\-—~～!！?？()（）【】\[\]「」『』"']/;
// 🎪 集名 → { num, date, split, variant, extra, extraKw, bare, residual }。
//   **关键(对抗审查三轮的核心)**:标记(上中下/纯享/预告/幕后…)只从【结构位置】认——紧贴集号/期号 token(glued)或独立成 token(分隔围起的纯标记),
//   绝不从自由文本副标题里扫。所以"第6集 幕后黑手"/"第5期 聊聊人生"/"幕后玩家"(电影) 的关键词都是内容,不当额外/变体 → 照常按集号/正片匹配,不丢弹幕。
function danmakuMarkers(s) {
    const raw = danmakuCleanEpName(s);
    const isDrama = /第\s*(?:\d+|[一二两三四五六七八九十百零]+)\s*[集话話]/.test(raw);
    const mdOk = (mm, dd) => +mm >= 1 && +mm <= 12 && +dd >= 1 && +dd <= 31;
    const pad = v => String(v).padStart(2, '0');
    let date = null, tokEnd = -1, dateStart = -1, dateEnd = -1, m;
    // dateStart 取【首个数字】位置(带 (?:^|\D) 前缀的规则 m.index 会多含一个非数字字符);dateEnd=日期 token 终点,供 num 去污染判独立性
    const dSpan = () => { dateStart = m.index + m[0].indexOf(m[1]); dateEnd = m.index + m[0].length; };
    if (isDrama) { const um = raw.match(/第\s*(?:\d+|[一二两三四五六七八九十百零]+)\s*[集话話]/); tokEnd = um.index + um[0].length; }
    else {
        if ((m = raw.match(/(?:^|\D)(\d{4})(\d{2})(\d{2})(?=\D|$)/)) && mdOk(m[2], m[3])) { date = m[1] + m[2] + m[3]; dSpan(); tokEnd = dateEnd; }
        else if ((m = raw.match(/(?:^|\D)(\d{2})(\d{2})(\d{2})(?=\D|$)/)) && mdOk(m[2], m[3])) { date = m[1] + m[2] + m[3]; dSpan(); tokEnd = dateEnd; }
        else if ((m = raw.match(/(\d{4})\s*[-./]\s*(\d{1,2})\s*[-./]\s*(\d{1,2})/)) && mdOk(m[2], m[3])) { date = m[1] + pad(m[2]) + pad(m[3]); dSpan(); tokEnd = dateEnd; }
        // "2017年7月1日"式:必须排在纯月日规则【之前】——否则年份被丢、date 只剩4位月日,绕过②的年份门禁(对抗审查实锤:事故B机制原样复活)
        else if ((m = raw.match(/(\d{4})\s*年\s*(\d{1,2})\s*月\s*(\d{1,2})\s*日?/)) && mdOk(m[2], m[3])) { date = m[1] + pad(m[2]) + pad(m[3]); dSpan(); tokEnd = dateEnd; }
        else if ((m = raw.match(/(\d{1,2})\s*月\s*(\d{1,2})\s*日?/)) && mdOk(m[1], m[2])) { date = pad(m[1]) + pad(m[2]); dSpan(); tokEnd = dateEnd; }
        else if ((m = raw.match(/(?:^|\D)(\d{2})(\d{2})\s*期/)) && mdOk(m[1], m[2])) { date = m[1] + m[2]; dSpan(); tokEnd = dateEnd; }
        // "2026-03期"月刊式:date=YYYYMM(6位,自然纳入②的年份门禁,只与同为YYYYMM的条目相等)。
        //   不识别的话 danmakuEpNum 回退首数字=年份2026,同年所有月份塌缩同号→固定串到第一期(对抗审查实锤)
        else if ((m = raw.match(/(\d{4})\s*[-./年]\s*(\d{1,2})\s*期/)) && +m[2] >= 1 && +m[2] <= 12) { date = m[1] + pad(m[2]); dSpan(); tokEnd = dateEnd; }
        const qi = raw.match(/第?\s*(?:\d{1,8}|[一二两三四五六七八九十百零]+)\s*期/);
        if (qi) tokEnd = Math.max(tokEnd, qi.index + qi[0].length);   // 期与日期并存(第5期20260101)取靠后者,别把日期当 residual
    }
    // 合集/连播条目(第1-2集 / 第2、3集 / 第1-2期)：时间轴=两集拼接,绝不能被单集号命中(错配)。num 置空 → 只能靠 ①a 原文全等(归一保留连字符)匹配同款合集。
    // 合集范围:两侧集/期号≤3位(4位是年份,"2026-01期"是月刊不是合集,别误判)
    const isRange = /(?<!\d)(?:\d{1,3}|[一二两三四五六七八九十百零]+)\s*[-—~～、,，]\s*(?:\d{1,3}|[一二两三四五六七八九十百零]+)\s*[集话話期]/.test(raw);
    let num = isRange ? null : danmakuEpNum(raw);
    // 🚨 num 去污染:集名带日期 token 时,num 只认【日期 token 之外】的独立 第N期/集 号。否则"6月24日"的 num=6(月份)
    //   会在源候选是纯期号式(日期配不上,②按设计不终结)时经③系统性撞上"第6期";"2026-03期"同理(num=年份)。
    //   "第5期20260101"/"20260101第5期"混合式的 5 来自日期 span 之外的独立 token,不受影响。
    if (num != null && date && dateStart >= 0 && !isDrama) {
        const indep = [...raw.matchAll(/第?\s*(?:0*\d{1,8}|[一二两三四五六七八九十百零]+)\s*[集话話期]/g)]
            .some(mm => mm.index >= dateEnd || mm.index + mm[0].length <= dateStart);
        if (!indep) num = null;
    }
    let split = '', variant = '', extra = false, extraKw = '', residual = false;
    if (tokEnd >= 0) {
        // 有 num/date/期/集 token：① glued run(token 紧贴其后到首分隔符,逐段剥前导标记) ② 独立 token(纯标记才认,否则 residual)
        const after = raw.slice(tokEnd), sepIdx = after.search(DM_SEP);
        let g = sepIdx < 0 ? after : after.slice(0, sepIdx);
        for (; g;) {
            if ((m = g.match(DM_VAR_RE))) { variant += m[0].toLowerCase(); g = g.slice(m[0].length); continue; }
            if ((m = g.match(DM_EXTRA_RE))) { extra = true; extraKw += m[0].toLowerCase(); g = g.slice(m[0].length); continue; }
            if ((m = g.match(/^([上中下])(?=$|[上中下]|[^一-龥])/))) { split += m[1]; g = g.slice(1); continue; }
            break;
        }
        const toks = ((g ? g + ' ' : '') + (sepIdx < 0 ? '' : after.slice(sepIdx))).split(DM_SEP).map(t => t.trim()).filter(Boolean);
        for (const tok of toks) {
            const core = tok.replace(/[集部篇赛场]+$/, '');
            if (/^[上中下]+$/.test(core)) split += core;
            else if (DM_TOK_VAR.test(core)) variant += core.toLowerCase();
            else if (DM_EXTRA_LABEL.test(tok) || DM_EXTRA_LABEL.test(core)) { extra = true; extraKw += dmExtraKw(tok); }   // "独家花絮"/"预告片" 等标签形态也认(修 第5集独家花絮 被当正片)
            else residual = true;
        }
    } else {
        // 无 num/date/期/集 token：纯 上集/下集(→split)、纯变体(→variant)、【标签形态】的额外内容(→extra)。
        //   额外只认"预告片/独家花絮/幕后花絮/花絮/彩蛋合集"这类【(可选短前缀)+额外词+(可选 片/版/集锦)】,
        //   绝不把"末日预告/终极预告/连锁反应"这种正常片名(内容词+关键词结尾)误判(对抗审查抓出的电影丢弹幕)。
        const w = raw.replace(/[集部篇赛场]+$/, '');
        if (/^[上中下]+$/.test(w)) split = w;
        else if (DM_TOK_VAR.test(w)) variant = w.toLowerCase();
        else if (DM_EXTRA_LABEL.test(raw) || DM_EXTRA_LABEL.test(w)) { extra = true; extraKw = dmExtraKw(raw); }
    }
    const bare = tokEnd >= 0 && !split && !variant && !extra && !residual;
    return { num, date, split, variant, extra, extraKw, bare, residual, range: isRange };
}
// 归一集名：去空格/括号/标点(小写)。数字间的连字符保留——"第1-2集"(合集)不能归一成"第12集"(对抗审查抓出的假命中)
function danmakuNormEp(s) { return String(s || '').replace(/[-—_](?!\d)|(?<!\d)[-—_]|[\s()（）\[\]【】·:：~～!！?？"'「」『』]/g, '').toLowerCase(); }
function danmakuDateEq(a, b) { return !!a && !!b && (a === b || a.endsWith(b) || b.endsWith(a)); }
function danmakuSufEq(a, b) { return a === b || (!!a && !!b && (a.includes(b) || b.includes(a))); }
// 📅 平台发布日期 + 时长认集(腾讯综艺):资源站常把综艺按播出日期命名(第20261010期),腾讯视频的集名却是"第1期上/第1期加更"、
//   不带日期 → 按集名永远配不上。腾讯选集接口每条都有发布日期和时长,但同一天腾讯常发好几条(正片/加更/纯享/陪看/采访/花絮…),
//   而 danmu_api 的集列表只有其中一部分。所以只在【我方是日期式集名 + 前端给了视频时长 + 这部剧在腾讯】时启用,并且:
//   拿腾讯【那一天所有标签】的条目,时长对得上、离得最近、与我方集名类别相容(纯享对纯享、第N期对第N期)的恰好一条才认,
//   直接按它的视频地址取弹幕(不要求它在 danmu_api 的集列表里);腾讯说不清就没有,不再退回别的平台按集名结构猜。
//   两轮对抗审查的实锤都在 scripts/danmaku-match-test.mjs ⑤⑥ 里。
function danmakuQqVid(url) {
    const m = String(url || '').match(/^https?:\/\/v\.qq\.com\/x\/cover\/([a-z0-9]+)\/([a-z0-9]+)\.html/i);
    return m ? { cid: m[1], vid: m[2] } : null;
}
// 腾讯选集接口(GetPageData vsite_episode_list)响应 → { items:[{vid,date,dur,trailer,title}], tabs:[{title,ctx,name,sub,key}], next }。
//   一页最多 30 条,has_next/next_page_context 是下一页。标签:单季节目是 正片/纯享/陪看/花絮特辑/直播回放…;长寿综艺是按季("2026秋"),
//   季里再分子标签(sub_chapter_name)。别的季(第1季/第2季…)若是别的 cid,标签不带 chapter_name,不要。同一标签每页的 ctx 字符串不同,按 key 去重。
function danmakuQqParseList(j) {
    const items = [], tabs = [], keys = new Set();
    let next = '';
    for (const mod of (j && j.data && j.data.module_list_datas) || []) {
        for (const md of (mod && mod.module_datas) || []) {
            let hasVid = false;
            for (const it of (md && md.item_data_lists && md.item_data_lists.item_datas) || []) {
                const p = (it && it.item_params) || {};
                if (p.vid) {
                    hasVid = true;
                    const dm = String(p.publish_date || '').match(/^(\d{4})-(\d{2})-(\d{2})/);
                    items.push({ vid: String(p.vid), date: dm ? dm[1] + dm[2] + dm[3] : '', dur: Math.round(Number(p.duration)) || 0, trailer: String(p.is_trailer) === '1', title: String(p.title || p.c_title_output || '') });
                } else if (p.page_context) {
                    let q = null;
                    try { q = new URLSearchParams(String(p.page_context)); } catch (e) { }
                    const name = q && q.get('chapter_name');
                    if (!name) continue;
                    const sub = q.get('sub_chapter_name') || '', key = name + '|' + sub;
                    if (keys.has(key)) continue;
                    keys.add(key);
                    tabs.push({ title: String(p.title || sub || name), ctx: String(p.page_context), name, sub, key });
                }
            }
            const mp = (md && md.module_params) || {};
            if (hasVid && !next && String(mp.has_next) === 'true' && mp.next_page_context) next = String(mp.next_page_context);
        }
    }
    return { items, tabs, next };
}
// 我方视频时长 ours ↔ 平台时长 theirs 对不对得上:资源站片源常比平台长 1–3%(插了广告/片头,短视频多 30–60s),个别站剪掉片头反而短 2–3%
function danmakuDurOk(ours, theirs) { return ours > 0 && theirs > 0 && ours >= theirs * 0.97 - 15 && ours <= theirs * 1.035 + 45; }
// 我方集名 → 要找的平台发布日期 YYYYMMDD;不是日期式、合集、或 4 位月日又不知道年份 → ''
function danmakuAirDateTarget(ep, preferYear) {
    const want = danmakuMarkers(ep);
    if (!want.date || want.range) return '';
    const py = String(preferYear || '');
    const t = want.date.length === 8 ? want.date : want.date.length === 6 ? '20' + want.date : (want.date.length === 4 && /^\d{4}$/.test(py) ? py + want.date : '');
    // "2026-03期"这类月刊式 danmakuMarkers 给的是 6 位 YYYYMM,当 YYMMDD 拼出来的月份不合法 → 不是某一天
    const mon = want.date.length === 6 && danmakuCleanEpName(ep).match(/(?:^|\D)((?:19|20)\d{2})\s*[-./年]\s*(\d{1,2})\s*期/);
    if (mon && want.date === mon[1] + mon[2].padStart(2, '0')) return '';
    const mo = +t.slice(4, 6), da = +t.slice(6, 8);
    return /^\d{8}$/.test(t) && mo >= 1 && mo <= 12 && da >= 1 && da <= 31 ? t : '';
}
// 剪辑类别词(纯享/陪看/花絮/直播回放…)。"加更"单独处理:平台写了加更、我方没写 → 照样相容(资源站按日期命名时常不写加更,
//   第20261012期 = 第1期加更);我方写了加更、平台没写 → 不相容(对抗审查:错标日期的加更会配到那天别的条目)
const DM_CUT_KW = ['纯享', '精编', '精华', '高光', '速看', '浓缩', '陪看', '直播', '花絮', '彩蛋', '预告', '采访', '番外', '超前', 'reaction'];
const danmakuQqHead = title => String(title || '').replace(/^【[^】]*】\s*/, '').split(/[：:]/)[0].toLowerCase();
// 期/集/日期后面的 上/中/下(中间可以隔着 加更/纯享/陪看/番外/花絮 或括号):第1期下纯享 → 下、第20261017期纯享上 → 上、第6期加更上 → 上、
//   20260601上 → 上、第10期中（上）→ 中。danmakuMarkers 的拆分要求后面不是汉字("第1期下纯享"认不出),这里单独认
function danmakuQqPart(s, isHead) {
    const m = String(s || '').match(/(?:期|集|(?:^|\D)(?:19|20)\d{6}|\d{1,2}日)\s*[（(]?\s*(?:(?:还有|特别)?加更|纯享|陪看|番外|花絮)?\s*[（(]?\s*([上中下])/);
    if (m) return m[1];
    // 平台标题末尾的 上/中/下 也算("心动的旅行中"、"先导片上";冒号后的副标题已被 danmakuQqHead 去掉)
    const t = isHead ? String(s || '').match(/([上中下])\s*(?:[（(·].*)?$/) : null;
    return t ? t[1] : '';
}
// 集名与平台条目的类别相不相容:2 = 严格相容(类别词两边一致);1 = 宽松(我方没写任何类别词、平台写了——资源站常把陪看/花絮/番外
//   也按日期命名,实测 60 多条);0 = 类别不相容(我方写了纯享/陪看/加更…而平台没写);-1 = 明确是另一条(两边都写了第N期却不是同一期,
//   或都写了 上/中/下 却不一样)
function danmakuAirDateCompatible(ep, title) {
    return danmakuAirDateStructOk(ep, title) ? danmakuAirDateCutLevel(ep, title) : -1;
}
function danmakuAirDateStructOk(ep, title) {
    const ours = danmakuCleanEpName(ep).toLowerCase(), head = danmakuQqHead(title);
    const wn = danmakuMarkers(ep).num, tn = danmakuMarkers(head).num;
    if (wn != null && tn != null && wn !== tn) return false;
    const wp = danmakuQqPart(ours), tp = danmakuQqPart(head, true);
    return !(wp && tp && wp !== tp);
}
function danmakuAirDateCutLevel(ep, title) {
    const ours = danmakuCleanEpName(ep).toLowerCase(), head = danmakuQqHead(title);
    if (ours.includes('加更') && !head.includes('加更')) return 0;
    let loose = false;
    for (const k of DM_CUT_KW) {
        if (ours.includes(k) && !head.includes(k)) return 0;
        if (!ours.includes(k) && head.includes(k)) loose = true;
    }
    if (loose && DM_CUT_KW.some(k => ours.includes(k))) return 0;   // 我方写了一种类别、平台是另一种
    return loose ? 1 : 2;
}
// 在平台某一天的【全部】条目里挑(dayItems 须是那天各标签合起来的全集),挑不出 → null(宁可没弹幕):
//   ① 时长对得上的条目里,严格相容的恰好一条 → 它;不止一条 → 我方写了 上/中/下 且只有一条拆分一致、而且它就是时长最近的那条
//     (或几条时长几乎一样、差 ≤5s,只能看拆分)→ 它。资源站片源常比平台长几十秒(插广告),两半时长差几十秒时光看哪条近靠不住
//   ② 一条严格相容的都没有、而整天只有一条时长对得上 → 宽松相容(我方没写类别词)也认
//   ③ 比选中那条更近(或几乎一样近,差 <5s)的条目里不能有类别不相容/宽松相容的(防"资源站把纯享按日期命名"拿到正片);
//     明确是另一条(-1:拆分/期号对不上)的不算——拆分标签比「哪条更近」可靠(资源站插广告会把我方时长拉长 13–120s,
//     对抗审查用去广告后的真实时长核对:标签一致的全对)
function danmakuAirDatePick(dayItems, ep, preferYear, dur) {
    const target = danmakuAirDateTarget(ep, preferYear);
    if (!target || !(dur > 0)) return null;
    const gap = it => Math.abs(dur - it.dur);
    const fits = (dayItems || []).filter(it => it.date === target && danmakuDurOk(dur, it.dur)).sort((a, b) => gap(a) - gap(b));
    if (!fits.length) return null;
    const lvl = new Map(fits.map(it => [it, danmakuAirDateCompatible(ep, it.title)]));
    const strict = fits.filter(it => lvl.get(it) === 2);
    let pick = null;
    if (strict.length === 1) pick = strict[0];
    else if (strict.length > 1) {
        const sp = danmakuQqPart(danmakuCleanEpName(ep).toLowerCase());
        let same = sp ? strict.filter(it => danmakuQqPart(danmakuQqHead(it.title), true) === sp) : [];
        const wn = danmakuMarkers(ep).num;
        if (same.length > 1 && wn != null) same = same.filter(it => danmakuMarkers(danmakuQqHead(it.title)).num === wn);
        if (same.length === 1 && (same[0] === strict[0] || Math.abs(same[0].dur - strict[0].dur) <= 5)) pick = same[0];
    } else if (fits.length === 1 && lvl.get(fits[0]) === 1) pick = fits[0];
    if (!pick) return null;
    for (const it of fits) {
        if (it === pick) continue;
        const l = lvl.get(it);
        if (l >= 0 && l !== 2 && gap(it) < gap(pick) + 5) return null;
    }
    return pick;
}
// 多实例赛跑怎么取舍(两后端共用,纯函数)。腾讯综艺日期式请求(dated):某实例按腾讯认集给了结论——认到了(_oracle)立即用,
//   认不出/腾讯没抓全(_veto)就以"没有"为准;别的实例没搜到腾讯候选、按旧规则猜的,要等全部实例回来,有 _veto 就作废
//   (对抗审查:那样猜常错,还会抢先赢下赛跑被存 7 天)。其余请求照旧:高贴合立即用,低贴合压 1.5s 等更好的。
function danmakuRaceVerdict(d, dated) {
    if (!d) return '';
    if (d._veto) return 'veto';
    if (!d.length) return '';
    if (d._oracle) return 'finish';
    if (dated) return 'holdAll';
    return (d._tier ?? 9) <= 1 ? 'finish' : 'hold';
}
function danmakuAirDated(title, ep, hints) {
    if (!(hints && Number(hints.dur) > 0)) return false;
    const yearM = String(title || '').match(/(?:19|20)\d{2}/);
    const py = yearM ? yearM[0] : ((hints && Number(hints.year) > 1900) ? String(Number(hints.year)) : '');
    return !!danmakuAirDateTarget(ep, py);
}
const danmakuVetoed = () => Object.assign([], { _veto: true });
// 这一次没取到是因为出错 / 超时(不是真没有):端点据此告诉前端"弹幕源没响应",而不是"本集暂无弹幕"
const danmakuFailed = () => Object.assign([], { _fail: true });
// 候选里这部剧的腾讯 cid:优先腾讯自己的候选(from tencent),否则取各候选腾讯地址里最常见的
function danmakuPoolQqCid(pool) {
    const cnt = new Map();
    let own = '';
    for (const a of (pool || []).slice(0, 3)) {
        const isQq = /from\s+(?:tencent|qq)\b/i.test(String(a && a.animeTitle || ''));
        for (const e of (a && a.episodes) || []) {
            const id = danmakuQqVid(e && e.url);
            if (!id) continue;
            if (isQq && !own) own = id.cid;
            cnt.set(id.cid, (cnt.get(id.cid) || 0) + 1);
        }
    }
    if (own) return own;
    let best = '', n = 0;
    cnt.forEach((c, k) => { if (c > n) { best = k; n = c; } });
    return best;
}
// danmu_api 的搜索按字面匹配:"现在就出发第四季"搜不到、"现在就出发第4季"才有(实测 2026-10-21,平台改了片名写法)。
//   搜不到时换写法再搜:季号 中文数字↔阿拉伯数字、"种地吧4"→"种地吧第4季"。最多 2 个;排序照旧拿我方原名比。
function danmakuTitleVariants(title) {
    const t = String(title || '').trim(), out = [];
    const add = v => { v = v.trim(); if (v && v !== t && !out.includes(v)) out.push(v); };
    let m = t.match(/^(.*?)\s*第\s*([一二两三四五六七八九十]+)\s*季(.*)$/);
    if (m && m[1].trim()) { const n = danmakuCn2Num(m[2]); if (n) { add(m[1] + '第' + n + '季' + m[3]); add(m[1] + ' 第' + n + '季' + m[3]); } }
    m = t.match(/^(.*?)\s*第\s*(\d{1,2})\s*季(.*)$/);
    if (m && m[1].trim()) { const cn = '零一二三四五六七八九十'; const n = +m[2]; if (n >= 1 && n <= 19) add(m[1] + '第' + (n <= 10 ? cn[n] : '十' + cn[n - 10]) + '季' + m[3]); }
    m = t.match(/^(.*[^\d\s])\s*([2-9])$/);
    if (m && !/第\s*\d+\s*季/.test(t)) add(m[1] + '第' + m[2] + '季');
    return out.slice(0, 2);
}
// episodes: [{episodeId,episodeTitle}]。epName=资源站集名。preferYear='2026'(可选,跨年同月日消歧)。
function pickDanmakuEpisode(episodes, epName, preferYear) {
    if (!episodes || !episodes.length) return null;
    const rawNorm = danmakuNormEp(epName || '');
    const cleaned = danmakuCleanEpName(epName || '').trim();
    const parts = episodes.map(e => ({ e, m: danmakuMarkers(e.episodeTitle), raw: danmakuNormEp(e.episodeTitle), n: danmakuNormEp(danmakuCleanEpName(e.episodeTitle)) }));
    // ①a 原文归一全等(不剥标签)：'第8期'配'第8期'不配'第8期会员版'；双语电影'粤语'配'粤语'不配'国语'
    let hit = rawNorm && parts.find(x => x.raw === rawNorm);
    if (hit) return hit.e;
    // ①b 剥标签后归一全等：跨写法('第10期(下)'↔'第10期下')、剥标签后同名
    const wn = danmakuNormEp(cleaned);
    hit = wn && parts.find(x => x.n && x.n === wn);
    if (hit) return hit.e;
    const want = danmakuMarkers(epName);
    want._norm = wn;   // 供 danmakuMoviePick 对多影片捆绑做模糊命中
    // 合集(第1-2期/第1-2集):时间轴=多集拼接,①a/①b 全等没配上就到此为止——绝不落入 moviePick,
    // 否则回退候选(同名电影/衍生片)的"正片"/唯一条目会被合集集名直接拿下(对抗审查实锤:两期综艺合集铺电影弹幕)
    if (want.range) return null;
    if (!epName || !cleaned) return danmakuMoviePick(parts, want);
    if (want.num == null && want.date == null) {
        if (want.split && !want.variant && !want.extra && !want.residual) {   // 纯"上集/下集/中集"→ 序数映射到正片
            const mains = parts.filter(x => !x.m.extra), bs = mains.find(x => x.m.split === want.split);
            if (bs) return bs.e;
            if (want.split === '中') return mains.length === 3 ? mains[1].e : null;
            if (mains.length >= 2 && mains.length <= 3) return want.split === '上' ? mains[0].e : mains[mains.length - 1].e;
            return null;
        }
        return danmakuMoviePick(parts, want);   // 电影/无结构
    }
    // 同号/同期候选池里按 变体/拆分/额外 挑
    const pick = (pool) => {
        const nonExtra = pool.filter(x => !x.m.extra), extras = pool.filter(x => x.m.extra);
        if (want.extra) {   // 我方是额外内容：只在额外条目里按子类型(花絮/预告/彩蛋)配
            if (!extras.length) return null;
            const same = extras.find(x => x.m.extraKw && want.extraKw && danmakuSufEq(want.extraKw, x.m.extraKw));
            if (same) return same.e;
            return (extras.length === 1 && !want.extraKw) ? extras[0].e : null;
        }
        if (want.variant) {   // 我方是变体(纯享/特辑…)：须同变体(精确/包含),缺则 null(绝不回落正片,时间轴不同)
            let h = nonExtra.find(x => x.m.variant === want.variant && x.m.split === want.split);
            if (h) return h.e;
            const compat = nonExtra.filter(x => x.m.variant && danmakuSufEq(want.variant, x.m.variant) && x.m.split === want.split);
            if (compat.length) { compat.sort((a, b) => b.m.variant.length - a.m.variant.length); return compat[0].e; }
            return null;
        }
        const bareSrc = nonExtra.find(x => x.m.bare);   // 源里【干净整集】条目(无拆分/变体/副标题) → 回落只认它,不认 上期回顾/下期精选 这种带副标题的异内容
        if (want.split) {   // 我方是 上/中/下 拆分
            const h = nonExtra.find(x => x.m.split === want.split && !x.m.variant);
            if (h) return h.e;
            if (nonExtra.some(x => x.m.split && !x.m.variant)) return null;   // 源本身按上中下拆分,但没我方这半 → 宁可没有
            // 源没拆分只有干净整集:仅"上"(与整集开头对齐)回落整集;"中/下"整集弹幕会整体前移半集偏移 → 宁可没有不错配
            return (want.split === '上' && bareSrc) ? bareSrc.e : null;
        }
        // 我方无标记：优先干净整集 → 同号唯一非拆分条目(可能带看点副标题,同集) → 纯期号(bare)时容忍源的 上/中/下 拆分取上
        if (bareSrc) return bareSrc.e;
        const plainish = nonExtra.filter(x => !x.m.split && !x.m.variant);
        if (plainish.length === 1) return plainish[0].e;
        if (want.bare) { const sp = nonExtra.filter(x => x.m.split && !x.m.variant); if (sp.length) { sp.sort((a, b) => '上中下'.indexOf(a.m.split[0]) - '上中下'.indexOf(b.m.split[0])); return sp[0].e; } }
        return null;
    };
    // ② 日期式期号(综艺)：同月日跨年 → 优先 preferYear、否则取最新一年；日期配不上【不终结】继续走 ③
    if (want.date) {
        let sd = parts.filter(x => danmakuDateEq(want.date, x.m.date));
        // 🚨 我方带明确年份(6/8位,如"第20170624期")：只认同样带年份且【同年同月日】(yymmdd 后缀相等)的集。
        //   纯月日式("0624期")一概不配——dateEq 的 endsWith 会让【任意年份】的同月日撞上;实测事故:
        //   iqiyi 正主瞬时限流返回空 → 候选回退到杂牌同名条目 → 其"0701期"式集名撞月日 → 拿到完全无关
        //   节目(转生史莱姆日记)的弹幕,再被 服务器+CDN+浏览器 三层缓存固化 7 天。宁可没有不错配。
        //   (纯月日 want——源站本来就只写"0624期"——保持原宽松逻辑,preferYear/最新年消歧。)
        if (sd.length && want.date.length >= 6) {
            const w6 = want.date.slice(-6);
            sd = sd.filter(x => x.m.date.length >= 6 && x.m.date.slice(-6) === w6);
        }
        if (sd.length) {
            const py = String(preferYear || ''), yy = py.slice(2);
            const byYear = py ? sd.filter(x => (x.m.date.length >= 8 && x.m.date.startsWith(py)) || (x.m.date.length === 6 && yy && x.m.date.startsWith(yy))) : [];
            if (byYear.length) sd = byYear;
            else { sd.sort((a, b) => (b.m.date.length - a.m.date.length) || b.m.date.localeCompare(a.m.date)); const latest = sd[0].m.date; sd = sd.filter(x => x.m.date === latest); }
            const r = pick(sd);
            if (r) return r;
            if (want.split || want.variant || want.extra) return null;
        }
    }
    // ③ 数字期/集号
    if (want.num != null) {
        const r = pick(parts.filter(x => x.m.num === want.num && !x.m.date));
        if (r) return r;
        if (want.split || want.variant || want.extra) return null;
        // 索引兜底：纯数字/第N集话/EP 且弹幕源集标题全无数字/日期,按序取第 N 个(目标位非额外内容)
        const numericSelf = (/[集话話]/.test(cleaned) || /^\s*(?:ep\.?\s*)?0*\d+\s*$/i.test(cleaned)) && !/期/.test(cleaned);
        if (numericSelf && !parts.some(x => x.m.num != null || x.m.date || x.m.range)) {
            // 按序取第 N 个,但索引到【剔除额外条目后】的数组(修:源开头挂预告片时 parts[n-1] 整体错位一集)
            const mains = parts.filter(x => !x.m.extra);
            if (want.num >= 1 && want.num <= mains.length) return mains[want.num - 1].e;
        }
        return null;
    }
    // 日期式集名(want.date)走到这=②年份门禁/日期匹配全拒——绝不落 moviePick:其"唯一条目/正片"兜底会把
    // 刚被门禁拒掉的异年候选原样捡回(对抗审查回归测试抓出的交互回归)。日期集名不是电影,宁空。
    return want.date ? null : danmakuMoviePick(parts, want);
}
// 电影/无集号兜底：我方额外内容→只配同子类型;否则 认准"正片"→唯一非额外条目→单条目。参数 parts 已含 marker。
function danmakuMoviePick(parts, want) {
    if (want && want.extra) {
        const extras = parts.filter(x => x.m.extra);
        if (!extras.length) return null;
        const same = extras.find(x => x.m.extraKw && want.extraKw && danmakuSufEq(want.extraKw, x.m.extraKw));
        if (same) return same.e;
        return (extras.length === 1 && !want.extraKw) ? extras[0].e : null;
    }
    const mains = parts.filter(x => !x.m.extra);
    const zheng = mains.find(x => /正片/.test(String(x.e.episodeTitle || '')));
    if (zheng) return zheng.e;
    if (mains.length === 1) return mains[0].e;
    if (mains.length > 1) {
        // 多条:先按 epName 模糊命中(不同影片被 danmu_api 捆在一个 anime 时,认准我方那部)
        const wn = want && want._norm;
        if (wn && wn.length >= 2) { const fz = mains.find(x => x.n && (x.n.includes(wn) || wn.includes(x.n))); if (fz) return fz.e; }
        // 剥标签后都为空/彼此相同 → 同片的版本(国语/粤语/画质,时间轴一致)取任一;否则是不同影片 → 宁可没有不错配
        const names = mains.map(x => danmakuCleanEpName(x.e.episodeTitle).trim());
        return names.every(n => !n || n === names[0]) ? mains[0].e : null;
    }
    return null;   // 源全是额外条目(预告/花絮),我方要正片 → 宁可没有(不拿预告弹幕铺正片)
}
// 🏅 弹幕候选排序(纯函数;scripts/danmaku-match-test.mjs 把它从 server.js / api/index.js 抽出来用真实候选回放,两份必须一致)。
//   danmu_api 按剧名搜出的候选 animeTitle 形如 "片名(年份)【类型】from 来源",这里挑出"就是我方这部"的那几个。
//   返回 { pool, bestTier, why }:pool = 最佳档内排好序的候选(调用方依次取集,最多试 3 个);bestTier 决定缓存多久。
//   贴合度分档:
//     0 精确同名(标点/繁体数字/罗马数字/海贼王↔航海王 已归一);
//     1 结构化等价 —— 去年份同名 / 季号写法不同(庆余年2↔第二季、仙剑奇侠传三↔第三部)/ 我方没写季号↔"第一季"、我方"第一季"↔裸名 /
//       年份式↔季号式 / 只差版本标签(未删减版、国语)/ "剧场版"位置不同 / 演员版本名且年份对得上 / 带[卫视版][全季]等标签的同名页;
//     2 只是名字互相包含(低置信:可能是续集/前传/同名别的作品,只短缓存);
//     9 不要:明确是别的季、电影↔非电影、路演/直播/花絮/纯享/小剧场等衍生内容、短剧撞名、年份差太多的翻拍。
//   hints(前端带来的我方信息;旧前端没有):type = 资源站分类(国产剧/大陆综艺/动作片/现代都市…),year = 资源站年份,eps = 我方集数。
//   规则全部用真实候选回放校过(scripts/fixtures/danmaku/real-cases.json:6 组约 200 例,读线上弹幕核对过内容)。原则:宁可没弹幕,不错配。
const DANMAKU_VERSION_ONLY = /^(?:(?:无删减|未删减|删减|完整|普通话|国语|粤语|沪语|闽南语|台语|原声|中字|中文字幕|双语|tv|加长|导演剪辑|会员|独播|4k|高清|蓝光|中配|日配|日语|英语|韩语|电视剧|剧集|hd|dvd)版?)+$/i;
// 衍生内容(不是这部作品本身的时间轴):路演直播、发布会、花絮、纯享/高光剪辑、解说、小剧场……
const DANMAKU_DERIVED = /路演|直播|发布会|特辑|幕后|花絮|预告|片花|采访|专访|访谈|解说|片段|混剪|剪辑|reaction|首映|彩蛋|纯享|精华|精编|高光|速看|浓缩|直拍|加更|plus|探班|看点|二创|赏析|盘点|vlog|回顾|小剧场|番外篇|周边|手办|制作特辑|合集/i;
// 我方自己就是剪辑版(纯享/精编/高光…):只有同样是这种剪辑的候选才对得上时间轴(held-out 实锤:纯享版配到了完整版)
const DANMAKU_EDIT = /纯享|精编|高光|精华|速看|浓缩|解说/;
function danmakuKindOfOurs(type, eps) {
    const t = String(type || '');
    let k = null;
    if (/综艺|真人秀|晚会|脱口秀/.test(t)) k = 'variety';
    else if (/动画片|动画电影|动漫电影|剧场版|电影版/.test(t)) k = 'movie';
    else if (/动漫|番剧|动画/.test(t)) k = 'anime';
    else if (/纪录|记录/.test(t)) k = null;                 // 纪录片既有单部也有系列,不判(弹幕源也常把纪录片标成综艺)
    else if (/片$|电影|影片/.test(t)) k = 'movie';          // 动作片/剧情片/喜剧片…(先于"剧":剧情片不是剧集)。信分类不信集数:有站把一部电影切成十几段
    else if (/短剧|现代都市|古装仙侠|穿越重生|女频|男频|爽剧|爽文|脑洞|战神|赘婿|甜宠|逆袭|萌宝|虐恋|总裁|神医|神豪|穿书/.test(t)) k = 'short';   // 短剧分类:常借名剧的名字(人世间/误杀/父母爱情1999);不放"年代/民国/宫斗"这类普通剧集也会用的词
    else if (/剧/.test(t)) k = 'tv';                        // 国产剧/韩剧/美剧/港剧/台剧/日剧/海外剧…
    if (!k && (Number(eps) || 0) >= 3) k = 'series';
    return k;
}
function danmakuKindOfCand(a) {
    const raw = String((a && a.animeTitle) || '');
    if (/剧场版|电影版|\bmovie\b|\bfilm\b/i.test(raw.replace(/【[^】]*】/g, ''))) return 'movie';   // 弹幕源常把动画电影标成【动漫】,看片名里的"剧场版"
    const m = raw.match(/【([^】]*)】/);
    const s = [a && a.typeDescription, a && a.type, m && m[1]].filter(Boolean).join(' ');
    if (/电影|movie/i.test(s)) return 'movie';
    if (/综艺/.test(s)) return 'variety';
    if (/动漫|动画|番剧|anime/i.test(s)) return 'anime';
    if (/电视剧|剧集|连续剧|\btv\b/i.test(s)) return 'tv';
    return null;
}
function danmakuRankCandidates(animes, title, hints) {
    hints = hints || {};
    const CN_DIGIT = { 壹: '一', 贰: '二', 叁: '三', 肆: '四', 伍: '五', 陆: '六', 柒: '七', 捌: '八', 玖: '九', 拾: '十' };
    const ROMAN = { Ⅰ: '1', Ⅱ: '2', Ⅲ: '3', Ⅳ: '4', Ⅴ: '5', Ⅵ: '6', Ⅶ: '7', Ⅷ: '8', Ⅸ: '9', Ⅹ: '10' };
    // 归一:去空白和标点(后宫·甄嬛传=后宫甄嬛传、神雕侠侣：问世间=神雕侠侣:问世间)、大写数字/罗马数字、海贼王=航海王
    const norm = s => String(s || '').replace(/[壹贰叁肆伍陆柒捌玖拾]/g, c => CN_DIGIT[c]).replace(/[ⅠⅡⅢⅣⅤⅥⅦⅧⅨⅩ]/g, c => ROMAN[c])
        .replace(/[\s·•・.。,，、:：;；!！?？'"‘’“”「」『』《》〈〉<>\-—–_~～/\\|]/g, '').toLowerCase().replace(/航海王/g, '海贼王');
    // 🏷️ danmu_api 的 animeTitle 常带 " from 平台" 尾巴——不剥掉的话 core/norm 精确档【永远打不中】,
    //    一切都掉进包含档(对抗审查实锤:韩国版/杂牌因此与正主同档,平台排序反而让错剧排前)。
    const stripFrom = s => String(s || '').replace(/\s+from\s+[a-z0-9_]+\s*$/i, '');
    const core = s => norm(String(stripFrom(s)).split(/[(（【\[]/)[0]);
    const normT = s => norm(stripFrom(s));
    const nt = norm(title), ct = core(title);
    // 片名后紧跟的 [..] / （..） 标签(长相思[全季]、漫长的季节[卫视版]、王牌对王牌（普通话）);年份括号不算
    const tagOf = a => { const m = stripFrom(a && a.animeTitle).match(/^[^(（【\[]*[\[（(]([^\]）)]*)[\]）)]/); return (m && !/^\s*(?:19|20)\d{2}\s*$/.test(m[1]) && !/^\s*0{3}\d\s*$/.test(m[1])) ? norm(m[1]) : ''; };
    // 季号解析成数字：认"第N季/第N部/Season N/SN" + 片名尾部裸数字("庆余年2"/"斗破苍穹4",排除 19xx/20xx 年份)。
    //   尾裸数字要看括号前的片名:候选是"庆余年2(2024)【电视剧】from 360",整串的结尾是"】"(旧版因此认不出候选的季号,
    //   "庆余年第二季"反而配到了"庆余年(2019)"= 第一季,真实数据回放实锤)
    // 片名里的年份:"天龙八部2003/快乐大本营2012"是版本/季的年份;但"请回答1988"(2015 年的剧)里 1988 是名字的一部分 ——
    //   比资源站年份早 2 年以上的当名字(不剥、不当年份用)。之后所有"剧名年份"都用 yearM(已排除名字里的年份)。
    const yearRaw = String(title).match(/(?:19|20)\d{2}/);
    const hintYear = Number(hints.year) > 1900 ? Number(hints.year) : 0;
    const yearInName = !!(yearRaw && hintYear && Number(yearRaw[0]) < hintYear - 1);
    const yearM = yearInName ? null : yearRaw;
    const seasonOf = s => { s = stripFrom(s); const m = s.match(/第\s*([0-9一二两三四五六七八九十]+)\s*[季部]|season\s*0*(\d+)|\bS0*(\d{1,2})\b/i); if (m) return danmakuCn2Num(m[1] || m[2] || m[3]); const t = s.split(/[(（【\[]/)[0].match(/(?<![0-9])([2-9]|1[0-9])\s*$/); return t ? parseInt(t[1], 10) : null; };
    const wantSeason = seasonOf(title);
    // 去掉季号后的名字(与 seasonOf 同口径):"庆余年第二季"/"庆余年2" → "庆余年"
    const SEASON_RE = /第[0-9一二两三四五六七八九十]+[季部]|season0*\d+|\bs0*\d{1,2}\b/gi;
    const unSeason = c => c.replace(SEASON_RE, '').replace(/(?<![0-9])([2-9]|1[0-9])$/, '');
    const baseOf = s => unSeason(core(s));
    const ctSeasonless = unSeason(ct);
    const CN_NUM = ['', '一', '二', '三', '四', '五', '六', '七', '八', '九', '十'];
    // 尾裸数字季号(庆余年2)去掉后用于包含匹配——否则弹幕源的"庆余年 第二季"(核心名不含"2")进不了候选,只剩第一季页 → 整季错配。
    const ctBase = wantSeason != null ? ct.replace(/([2-9]|1\d)$/, '') : ct;
    // 尾缀年份综艺名(王牌对王牌2024):去年份后才可能与"王牌对王牌 第九季"互相包含(否则正主进不了候选、只剩裸基名=第一季 → 整季串台,对抗审查实锤)
    const ctNoYear = yearInName ? ct : ct.replace(/((?:19|20)\d{2})\s*$/, '');
    const unMovie = c => c.replace(/剧场版|电影版/g, '');
    // 我方年份:剧名里的年份(快乐大本营2012 / 天龙八部2003)比资源站 vod_year(常是开播年)更具体
    const ourYear = (yearM ? Number(yearM[0]) : 0) || hintYear;
    // 我方自己是剪辑版(纯享/精编…)时,候选也必须是同一种剪辑
    const ourEdit = (ct.match(DANMAKU_EDIT) || [])[0] || '';
    const ourEps = Number(hints.eps) || 0;
    const epCount = a => (a && Array.isArray(a.episodes)) ? a.episodes.length : null;
    const yearOf = a => { const m = String((a && a.animeTitle) || '').match(/[(（]((?:19|20)\d{2})[)）]/); return m ? Number(m[1]) : null; };
    const junkYear = a => /[(（]0{3}\d[)）]/.test(String((a && a.animeTitle) || ''));   // "海贼王系列(0001)"这类年份为 0 的杂项条目
    const yDist = a => { const y = yearOf(a); return (ourYear && y) ? Math.abs(y - ourYear) : null; };
    const remOf = (c, stem) => {   // 两名互相包含时,多出来的那截;不包含返回 null
        if (!stem || !c || c === stem) return null;
        return c.includes(stem) ? c.replace(stem, '') : (stem.includes(c) ? stem.replace(c, '') : null);
    };
    const derived = r => !!r && DANMAKU_DERIVED.test(r) && !DANMAKU_DERIVED.test(ct);
    // 🏅 名字贴合度分档(见函数头注释)
    const fitTier = a => {
        const c = core(a.animeTitle);
        if (!c) return 9;
        const tag = tagOf(a);
        if (ourEdit && !c.includes(ourEdit) && !tag.includes(ourEdit)) return 9;   // 我方纯享版/精编版 ≠ 完整版
        if (derived(tag)) return 9;
        const tagged = !!tag && !DANMAKU_VERSION_ONLY.test(tag);
        if (c === ct || normT(a.animeTitle) === nt) return tagged ? 1 : 0;
        const s = seasonOf(a.animeTitle), bc = baseOf(a.animeTitle);
        const r1 = remOf(c, ct), r2 = ctNoYear !== ct ? remOf(c, ctNoYear) : null;
        if (derived(r1) || derived(r2)) return 9;   // 路演直播/花絮/纯享/小剧场……不是这部作品的时间轴
        // "XX之YY" 多出来的是"之…"副标题 = 续作/衍生(爸爸去哪儿第三季之听爸爸的话、唐朝诡事录之西行、鬼吹灯之精绝古城)
        if ((r1 && /^之/.test(r1)) || (r2 && /^之/.test(r2))) return 9;
        if (ctNoYear && ctNoYear !== ct && c === ctNoYear) return 1;
        //   候选名自带年份尾巴("误杀 2019(2019)"):去掉后与我方同名、且这个年份就是它自己的年份
        { const cy = c.match(/((?:19|20)\d{2})$/); if (cy && c.slice(0, -4) === ct && yearOf(a) === Number(cy[1])) return 1; }
        //   同一部的不同版本名(知否…网络版 ↔ 知否… DVD版):两边各去掉结尾一个"XX版"后同名、年份对得上 → 结构化等价(再靠集数挑对剪辑)
        { // 逐个长度试"去掉结尾 1~6 字 + 版"(正则贪婪会多剥:知否…绿肥红瘦dvd版 会被剥成"知否知否应是绿")
          const stems = x => { const out = new Set([x]); if (/版$/.test(x)) for (let k = 1; k <= 6 && k < x.length - 1; k++) out.add(x.slice(0, x.length - 1 - k)); return out; };
          const sc = stems(c), dd = yDist(a);
          if (dd != null && dd <= 1 && !/剧场|电影/.test(c + ct) && [...stems(ct)].some(x => x.length >= 3 && sc.has(x) && (x !== c || x !== ct))) return 1; }
        // 明确是别的季:我方没写季号(=第一季/第一部),候选写着第 2 季以上(长相思 第二季、斗罗大陆2绝世唐门 动态漫画 第5季)→ 不同季,不要
        if (wantSeason == null && s != null && s >= 2 && (bc === ct || c.includes(ct))) return 9;
        // ① 季号写法不同:两边季号都认得出且相同、去掉季号后同名(庆余年2 ↔ 庆余年第二季;旧版"第二季→2"方向根本配不上)
        if (wantSeason != null && s === wantSeason && bc && bc === ctSeasonless) return 1;
        //   中文数字结尾 ↔ 第N部/季:仙剑奇侠传三 ↔ 仙剑奇侠传 第三部(两个方向)
        if (s != null && s >= 2 && s <= 10 && bc && (ct === bc + CN_NUM[s] || ct === bc + s)) return 1;
        if (wantSeason != null && wantSeason >= 2 && wantSeason <= 10 && s == null && (c === ctSeasonless + CN_NUM[wantSeason])) return 1;
        //   第一季 ↔ 裸名:我方没写季号 ↔ 候选"第一季";我方"第一季" ↔ 候选裸名
        if (wantSeason == null && s === 1 && bc === ct) return 1;
        if (wantSeason === 1 && s == null && (c === ctSeasonless || c === ctSeasonless + '1')) return 1;   // 爱情公寓第一季 ↔ 爱情公寓1
        // ② 年份式 ↔ 季号式:我方剧名带年份,候选标题带同一年份,去掉季号后同名
        if (yearM && ctNoYear !== ct && String(a.animeTitle).includes(yearM[0]) && bc === unSeason(ctNoYear)) return 1;
        // ③ 只差版本标签(未删减版/国语/粤语/TV版…);"剧场版"位置不同(咒术回战0 剧场版 ↔ 剧场版 咒术回战0)
        if ((r1 && DANMAKU_VERSION_ONLY.test(r1)) || (r2 && DANMAKU_VERSION_ONLY.test(r2) && String(a.animeTitle).includes(yearM[0]))) return 1;
        if (/剧场版|电影版/.test(c + ct) && unMovie(c) === unMovie(ct)) return 1;
        // ④ 演员/版本名("胡军版"/"黄日华版"):同名翻拍的版本标记,只有年份对得上才算这一部
        const d = yDist(a);
        if (((r1 && /^.{1,6}版$/.test(r1)) || (r2 && /^.{1,6}版$/.test(r2))) && d != null && d <= 1) return 1;
        // 名字互相包含(或去季号/去年份后包含)—— 低置信。两个字的名字太容易被包含(死神 ⊂ 死神少爷与黑女仆、狂飙 ⊂ 狂飙兄弟),不认
        const contains = c.includes(ct) || ct.includes(c)
            || (ctBase !== ct && ctBase && c.includes(ctBase))
            || (ctNoYear !== ct && ctNoYear && (c.includes(ctNoYear) || ctNoYear.includes(c)));
        if (contains && Math.min(c.length, (ctNoYear || ct).length) > 2) return 2;
        return 9;
    };
    // 🎬 类型:
    //   硬冲突只有"电影 ↔ 非电影"(综艺"王牌对王牌"绝不能拿 1998 年同名电影的弹幕);
    //   其它先找同类型(剧集≠动漫:苍兰诀/三体/大奉打更人 的电视剧与动画同名同年),没有同类型才放宽到相近类型(剧集~动漫~短剧)
    let ourKind = danmakuHintKind(hints);
    // 片名自带的版本标记比资源站分类可靠:"苍兰诀（动画版）"有站标成内地剧,"凡人修仙传真人版"有站标成动漫(实测)
    if (/动画版|动漫版/.test(String(title)) && ourKind !== 'movie') ourKind = 'anime';
    else if (/真人版|电视剧版/.test(String(title)) && (ourKind === 'anime' || ourKind === 'series' || !ourKind)) ourKind = 'tv';
    if (/剧场版|电影版/.test(String(title)) && ourKind !== 'variety') ourKind = 'movie';   // 我方片名自带"剧场版"(分类常写成国产动漫)
    const isMovie = k => k === 'movie';
    // 综艺 ↔ 非综艺 也是硬冲突(新西游记 第八季 ≠ 西游记(1986)电视剧;天龙八部(2009)【综艺】≠ 天龙八部电视剧)
    const isVariety = k => k === 'variety';
    const near = k => (ourKind === 'series' || ourKind === 'tv' || ourKind === 'anime' || ourKind === 'short') && (k === 'tv' || k === 'anime');
    // 动画电影(动画片/动漫电影/剧场版):弹幕源常把它标成【动漫】(熊出没·重启未来),名字精确/结构化等价时也认
    const animatedMovie = ourKind === 'movie' && (hints.kind === 'amovie' || /动画|动漫/.test(String(hints.type || '')) || /剧场版/.test(String(title)));
    let candidates = (animes || []).filter(a => {
        if (fitTier(a) >= 9) return false;
        const k = danmakuKindOfCand(a);
        if (!ourKind || !k) return true;
        if (ourKind === 'series') return !isMovie(k);   // 只知道是多集:排除电影即可
        if (animatedMovie && k === 'anime') { const n = epCount(a); return fitTier(a) === 0 && (n == null || n <= 3); }   // 鬼灭之刃 无限列车篇【动漫】是 7 集 TV 版,不是剧场版
        return isMovie(ourKind) === isMovie(k) && isVariety(ourKind) === isVariety(k);
    });
    if (ourKind && ourKind !== 'series') {
        const exactKind = ourKind === 'short' ? 'tv' : ourKind;
        if (candidates.some(a => danmakuKindOfCand(a) === exactKind)) candidates = candidates.filter(a => { const k = danmakuKindOfCand(a); return !k || k === exactKind; });
        else if (candidates.some(a => near(danmakuKindOfCand(a)))) candidates = candidates.filter(a => { const k = danmakuKindOfCand(a); return !k || near(k); });
    }
    // 🗓️ 年份偏好(在分档之前——标题带年份时,含该年份的候选是最强信号:"王牌对王牌2024"该选"第九季(2024)"而不是裸基名第一季页)
    if (candidates.length > 1 && yearM) { const withYear = candidates.filter(a => String(a.animeTitle || '').includes(yearM[0])); if (withYear.length) candidates = withYear; }
    // 🗓️ 季号/续集号：先取精确同季(我方"第一季"时裸名也算第一季);没有精确同季时【无论单/多候选】剔除 裸基名(第一部/第一季)和季号明确不同的——
    //    它们是不同作品,宁可没弹幕不错配。(单候选旁路已修:明确异季的唯一候选此前会被原样保留,对抗审查实锤)
    if (wantSeason != null && candidates.length) {
        const exact = candidates.filter(a => { const s = seasonOf(a.animeTitle); return s === wantSeason || (wantSeason === 1 && s == null && core(a.animeTitle) === ctSeasonless) || fitTier(a) <= 1; });
        if (exact.length) candidates = exact;
        // 裸基名(去掉季号后与我方同名、自己不带季号)= 第一季,要第 2 季以上时不要
        else candidates = candidates.filter(a => { const s = seasonOf(a.animeTitle); const c = core(a.animeTitle); return (s == null || s === wantSeason) && c !== ctBase && !(wantSeason >= 2 && s == null && c === ctSeasonless); });
    }
    const platOf = s => { const m = String(s || '').match(/from\s+([a-z0-9]+)/i); return m ? m[1].toLowerCase() : ''; };
    const PLAT_RANK = { iqiyi: 0, qq: 1, tencent: 1, youku: 2, bilibili: 3, mango: 4, imgo: 4, '360': 5, migu: 9 };
    // 排序:贴合档 → 不带标签的 → 年份接近 → 平台弹幕量;回退循环只在【最佳档】内轮换——iqiyi 正主瞬时空 → 同档 qq 接棒(合法多平台回退),
    // 绝不落到包含档杂牌(对抗审查实锤:正主瞬时空时杂牌错弹幕被回退捡走并 LONG_CACHE 固化 7 天)。
    const yKey = a => { const d = yDist(a); return d == null ? 50 : d; };
    const tagKey = a => { const t = tagOf(a); return (t && !DANMAKU_VERSION_ONLY.test(t)) ? 1 : 0; };
    candidates.sort((a, b) => (fitTier(a) - fitTier(b)) || (tagKey(a) - tagKey(b)) || (yKey(a) - yKey(b))
        || ((PLAT_RANK[platOf(a.animeTitle)] ?? 6) - (PLAT_RANK[platOf(b.animeTitle)] ?? 6)));
    // 🗓️ 翻拍/重名:我方有年份时,逐档找"年份对得上"的;某档全是差太多的就看下一档。容差:精确同名 ≤3 年(弹幕源有时写出品年,
    //    神雕侠侣:问世间 差 3 年),结构化/低置信 ≤1 年。综艺(一个页面跨很多年)与类型未知(纪录片常被标成综艺、年份是上架年)只排序不剔。
    //    年份未知的候选不因年份被剔。短剧只认精确/结构化且年份 ≤1(它们常借名剧的名字)。
    const yearStrict = ourYear && ourKind && ourKind !== 'variety';
    const exactKind = ourKind === 'short' ? 'tv' : ourKind;
    const isPlainName = a => { const c = core(a.animeTitle); return !tagKey(a) && (c === ct || c === ctNoYear); };
    let rejected = '';
    const epsOk = a => { const n = epCount(a); return n != null && Math.abs(n - ourEps) <= 1; };
    const epsMatchT1 = ourEps >= 3 && candidates.some(a => fitTier(a) === 1 && epsOk(a));
    for (const tier of [0, 1, 2]) {
        if (ourKind === 'short' && tier >= 2) break;
        let pool = candidates.filter(a => fitTier(a) === tier);
        // 年份为 0 的杂项条目("海贼王系列(0001)")只在名字精确时才认(短剧常就是 0001)
        if (tier >= 1 && ourYear) pool = pool.filter(a => !junkYear(a));
        // 低置信档只认同类型(封神榜2000 电视剧 ≠ 封神榜传奇(2000)动画)
        if (tier >= 2 && ourKind && ourKind !== 'series') pool = pool.filter(a => { const k = danmakuKindOfCand(a); return !k || k === exactKind; });
        // 年份式命名的综艺(花儿与少年2026):低置信档必须同一年(别的季常只差一年)
        if (tier >= 2 && ourKind === 'variety' && yearM) pool = pool.filter(a => yDist(a) === 0);
        if (!pool.length) continue;
        if (tier === 0 && epsMatchT1 && pool.every(a => epCount(a) != null && !epsOk(a))) continue;   // 少年神探狄仁杰 40 集 ↔ DVD版 40 集,不是 36 集播出版
        if (yearStrict) {
            const lim = ourKind === 'short' ? 1 : (tier === 0 ? 3 : 1);
            const ok = pool.filter(a => { const d = yDist(a); return d == null ? (ourKind !== 'short' || tier === 0) : d <= lim; });
            if (!ok.length) { rejected = 'year-mismatch'; continue; }
            pool = ok;
        }
        // 同一部的不同剪辑(少年神探狄仁杰 DVD版 40 集 / 播出版 36 集):集数对得上(±1)的优先,对不上的分集会错位
        const byEps = ourEps >= 3 ? pool.filter(epsOk) : [];
        if (byEps.length) pool = byEps;
        else {
            const plain = pool.filter(a => !tagKey(a));
            if (plain.length) pool = plain;   // 同档里有不带[卫视版][全季]标签的正片页就只用它(标签页常是不同剪辑/合集)
            const exact = pool.filter(isPlainName);
            if (exact.length) pool = exact;   // 有和我方同名的正片页就不要"XX字幕版/XX版"变体(天天向上2019 ↔ 天天向上 越南语字幕版)
        }
        // 只知道是多集(或完全没提示)时,同档里剧集/动漫/综艺/电影混在一起 = 分不出是哪部(苍兰诀 电视剧与动画同名同年)→ 宁可不选
        //   (从历史/离线续看时没有分类提示,旧版会随手挑一个并长缓存 7 天,审查实锤)
        if ((!ourKind && !hints.type && !hints.kind) || ourKind === 'series') {
            const kinds = new Set(pool.map(danmakuKindOfCand).filter(Boolean));
            if (kinds.size > 1) return { pool: [], bestTier: 9, why: 'ambiguous-kind' };
        }
        return { pool, bestTier: tier, why: `tier${tier}${ourKind ? ' kind=' + ourKind : ''}${ourYear ? ' year=' + ourYear : ''}` };
    }
    return { pool: [], bestTier: 9, why: rejected || (candidates.length ? 'filtered' : 'no-candidate') };
}
// 前端提示里的类型:v5 新前端直接送归一后的 k:(tv/anime/movie/amovie=动画电影/variety/short/series),旧的只送资源站分类 t:
function danmakuHintKind(hints) {
    if (hints && hints.kind) return hints.kind === 'amovie' ? 'movie' : hints.kind;
    return danmakuKindOfOurs(hints && hints.type, hints && hints.eps);
}
// 弹幕请求 id 解析(两后端共用,纯函数):剧名|集名|版本[|k:类型|t:资源站分类|y:年份|n:集数|d:我方视频时长秒]。只认这几个前缀,其它段忽略。
//   缓存键只带真正影响匹配的部分(类型 + 年份):同名的综艺与电影、不同年份的翻拍各自缓存;集数会随更新变,不进键。
function danmakuParseId(id) {
    const hints = {};
    let title = '', ep = '';
    try {
        const parts = String(id || '').split('|'); title = (parts[0] || '').trim(); ep = (parts[1] || '').trim();
        for (const p of parts.slice(2)) {
            const m = String(p).match(/^([ktynd]):(.{1,40})$/);
            if (!m) continue;
            if (m[1] === 't') hints.type = m[2].trim();
            else if (m[1] === 'k' && /^(tv|anime|movie|amovie|variety|short|series)$/.test(m[2])) hints.kind = m[2];
            else if (m[1] === 'y' && /^(19|20)\d{2}$/.test(m[2])) hints.year = Number(m[2]);
            else if (m[1] === 'n' && /^\d{1,5}$/.test(m[2])) hints.eps = Number(m[2]);
            else if (m[1] === 'd' && /^\d{2,5}$/.test(m[2]) && +m[2] >= 30) hints.dur = Number(m[2]);   // 我方视频时长(秒),见 danmakuAirDatePick
        }
    } catch (e) { }
    const k = hints.kind || danmakuKindOfOurs(hints.type, hints.eps);
    // 日期式集名 + 时长:结果取决于时长(同名的不同剪辑认到不同条目),缓存键带上时长档(按 4% 分档;不同站同一条片源可能落在相邻两档,只是多抓一次)。
    //   其余(不带时长、非日期式)键与以前完全一样,旧缓存照用。
    const yearM = title.match(/(?:19|20)\d{2}/);
    const py = yearM ? yearM[0] : (hints.year ? String(hints.year) : '');
    const qd = hints.dur && danmakuAirDateTarget(ep, py) ? '|qd' + Math.round(Math.log(hints.dur) / Math.log(1.04)) : '';
    const cacheKey = title + '|' + ep + (k ? '|k:' + k : '') + (hints.year ? '|y:' + hints.year : '') + qd;
    return { title, ep, hints, cacheKey };
}
// 🏷️ 这一集弹幕的平台来源(两后端共用,纯函数):前端只对芒果(imgo)做按集自动校正 —— 芒果弹幕的时间轴和多数线路过 Worker 后一致,腾讯等不一致
//   (见 index.html <dg-dm-auto-core>)。集条目形如 { episodeTitle:'【imgo】 第1集', url:'https://www.mgtv.com/…' }。
//   取弹幕用的是地址,所以先认地址、再认标签;两边说的不是一个平台(合并源之类)一律当不确定('')。标签要在集名最前面,片名里的 【】 不算。
const DANMAKU_SRC_HOSTS = [[/(^|\.)mgtv\.com$/, 'imgo'], [/(^|\.)qq\.com$/, 'qq'], [/(^|\.)iqiyi\.com$/, 'qiyi'], [/(^|\.)youku\.com$/, 'youku'], [/(^|\.)(bilibili\.com|b23\.tv)$/, 'bilibili'], [/(^|\.)miguvideo\.com$/, 'migu'], [/(^|\.)sohu\.com$/, 'sohu'], [/(^|\.)le\.com$/, 'leshi'], [/(^|\.)ixigua\.com$/, 'xigua']];
function danmakuSourceOf(episode) {
    const e = episode || {};
    const m = String(e.episodeTitle || '').match(/^\s*【([a-z0-9_]{1,16})】/i);
    const tag = m ? m[1].toLowerCase() : '';
    let host = '';
    try { host = new URL(String(e.url || '')).hostname.toLowerCase(); } catch (err) { }
    const hit = host ? DANMAKU_SRC_HOSTS.find(x => x[0].test(host)) : null;
    const byHost = hit ? hit[1] : '';
    if (byHost && tag && !tag.startsWith(byHost)) return '';
    return byHost || tag;
}
// ⛔ 以下联网(非纯函数),scripts/danmaku-match-test.mjs 抽取的纯函数区到此为止
// 腾讯选集接口一页。同一页全站共享:并发只打一次、固定 5s 超时(不随调用方剩余时间缩短,慢页照样落进缓存给后来的人用)。
//   成功缓存 30 分钟;过期或要求更新(maxAge)时重拉,重拉失败继续用旧的(6 小时内;1 分钟内不再重试);没成功过的失败只记 30 秒。
const danmakuQqPageCache = new Map();
const danmakuQqCidMemo = new Map();   // 剧名|年份 -> { cid, expiry }:某个实例的候选里认出过腾讯 cid,别的实例(候选里没有腾讯)也拿来用
const DANMAKU_QQ_TTL = 30 * 60 * 1000, DANMAKU_QQ_FAIL_TTL = 30 * 1000, DANMAKU_QQ_STALE_MAX = 6 * 3600e3;
function danmakuQqFetch(cid, ctx) {
    return axios.post('https://pbaccess.video.qq.com/trpc.universal_backend_service.page_server_rpc.PageServer/GetPageData?video_appid=3000010&vplatform=2&vversion_name=8.2.96',
        { page_params: { req_from: 'web_vsite', page_id: 'vsite_episode_list', page_type: 'detail_operation', id_type: '1', page_size: '', cid, vid: '', lid: '', page_num: '', page_context: ctx || '', detail_page_type: '1' }, has_cache: 1 },
        { timeout: 5000, headers: { 'Content-Type': 'application/json', 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36', Referer: 'https://v.qq.com/', Origin: 'https://v.qq.com' } })
        .then(r => { const v = danmakuQqParseList(r.data); return (v.items.length || v.tabs.length) ? v : null; })
        .catch(e => { console.warn(`[弹幕诊断] 腾讯选集 ${cid} 失败: ${e.code || ''} ${e.response ? 'HTTP' + e.response.status : e.message}`); return null; });
}
// 这一页现在去拿会不会直接命中缓存(不发请求)——页数上限只算真发出去的请求
function danmakuQqPeek(cid, ctx, maxAge) {
    const c = danmakuQqPageCache.get(cid + '|' + (ctx || '')), now = Date.now();
    return !!c && c.expiry > now && !(maxAge && c.ok && now - c.at > maxAge);
}
function danmakuQqPage(cid, ctx, maxAge) {
    const key = cid + '|' + (ctx || ''), now = Date.now(), c = danmakuQqPageCache.get(key);
    if (c) {
        if (c.expiry > now && !(maxAge && c.ok && now - c.at > maxAge)) return c.p;
        if (c.ok && now - c.at < DANMAKU_QQ_STALE_MAX) {
            if (c.refreshing) return c.refreshing;
            if (c.retryAt && now < c.retryAt) return c.p;
            c.refreshing = danmakuQqFetch(cid, ctx).then(v => {
                c.refreshing = null;
                if (v) { danmakuQqPageCache.set(key, { p: Promise.resolve(v), ok: true, at: Date.now(), expiry: Date.now() + DANMAKU_QQ_TTL }); return v; }
                c.retryAt = Date.now() + 60000;
                return c.p;
            });
            return c.refreshing;
        }
        if (c.expiry > now) return c.p;
    }
    const ent = { p: null, ok: false, at: now, expiry: now + DANMAKU_QQ_TTL };
    ent.p = danmakuQqFetch(cid, ctx).then(v => { if (v) ent.ok = true; else ent.expiry = Date.now() + DANMAKU_QQ_FAIL_TTL; return v; });
    if (danmakuQqPageCache.size >= 400) { const k = danmakuQqPageCache.keys().next().value; if (k !== undefined) danmakuQqPageCache.delete(k); }
    danmakuQqPageCache.set(key, ent);
    return ent.p;
}
// 腾讯某一天的全部条目(各标签合起来)。status:complete = 各标签都翻过了这一天;partial = 没翻全(超时/页数/某页失败/找不到那一季);
//   failed = 首页就拿不到。只有 complete 才拿来认集(没翻全时"唯一对得上"不可信,对抗审查实锤)。
//   单季节目:默认链(正片)与其余各标签并行翻;长寿综艺(标签是"2026秋"这种):找包含这一天的那一季(标题含目标年份的、再加它前一个——
//   冬季跨年;都不含就试最新一季),这一天落在某季正片最后一期之后两周内也算那一季(这周的花絮/特辑挂在它的子标签里),再翻那一季的各子标签。
//   每个标签沿分页翻到越过目标日期为止(升序降序都认)。真发出去的请求最多 16 个,deadline 为止。
//   目标比已知最新的正片还晚、又在两周内 → 多半是刚上线的新一期而缓存是旧页,比 3 分钟旧的重拉一遍。
async function danmakuQqDay(cid, target, deadline) {
    const day = new Map();
    let pages = 0, newestReal = '';
    const get = async (ctx, maxAge) => {
        const left = deadline - Date.now();
        if (left < 300) return undefined;
        if (!danmakuQqPeek(cid, ctx, maxAge)) { if (pages >= 16) return undefined; pages++; }
        let timer = null;
        const late = new Promise(res => { timer = setTimeout(() => res(undefined), left); });
        const r = await Promise.race([danmakuQqPage(cid, ctx, maxAge), late]);
        clearTimeout(timer);
        return r;   // null = 失败;undefined = 没时间/没额度
    };
    const take = r => { for (const it of r.items) { if (it.date === target) day.set(it.vid, it); if (!it.trailer && it.date > newestReal) newestReal = it.date; } };
    const walk = async (r, maxAge) => {
        for (;;) {
            if (!r) return false;
            take(r);
            if (!r.next || !r.items.length) return true;
            const a = r.items[0].date, b = r.items[r.items.length - 1].date;
            if (a <= b ? b > target : b < target) return true;
            r = await get(r.next, maxAge);
        }
    };
    const days = (a, b) => (Date.UTC(+b.slice(0, 4), +b.slice(4, 6) - 1, +b.slice(6, 8)) - Date.UTC(+a.slice(0, 4), +a.slice(4, 6) - 1, +a.slice(6, 8))) / 864e5;
    const crawl = async maxAge => {
        const d0 = await get('', maxAge);
        if (d0 === null) return 'failed';
        if (!d0) return 'partial';
        take(d0);
        const tabs = d0.tabs.filter(t => !t.sub);
        const seasons = tabs.filter(t => /(?:19|20)\d{2}/.test(t.title));
        if (seasons.length) {
            const y = target.slice(0, 4), pick = [];
            seasons.forEach((t, i) => { if (t.title.includes(y)) pick.push(i); });
            if (pick.length && pick[0] > 0) pick.unshift(pick[0] - 1);
            if (!pick.length) pick.push(seasons.length - 1);
            // 每一季:首页的最后一期还早于目标、又有下一页 → 先沿分页翻到越过目标,这一季的日期范围按翻到的全部算
            const rs = await Promise.all(pick.map(async i => {
                const r = await get(seasons[i].ctx, maxAge);
                if (!r) return { r };
                const all = r.items.slice();
                let cur = r, okS = true;
                while (cur && cur.next && cur.items.length && cur.items[cur.items.length - 1].date < target) {
                    cur = await get(cur.next, maxAge);
                    if (!cur) { okS = false; break; }
                    take(cur);
                    all.push(...cur.items);
                }
                return { r, all, okS };
            }));
            let ok = true, hit = null, before = null;
            for (const { r, all, okS } of rs) {
                if (!r) { ok = false; continue; }
                if (!okS) ok = false;
                take(r);
                const ds = all.map(x => x.date).filter(Boolean).sort();
                if (!ds.length) continue;
                const lo = ds[0], hi = ds[ds.length - 1];
                if (lo <= target && target <= hi) hit = r;
                else if (hi < target && days(hi, target) <= 14 && (!before || hi > before.hi)) before = { r, hi };
            }
            if (!hit && before) hit = before.r;
            if (!hit) return 'partial';
            const subs = hit.tabs.filter(t => t.sub && t.sub !== '正片');
            const done = await Promise.all([walk(hit, maxAge), ...subs.map(async t => walk(await get(t.ctx, maxAge), maxAge))]);
            return ok && done.every(Boolean) ? 'complete' : 'partial';
        }
        const others = tabs.filter(t => t.name !== '正片');
        const done = await Promise.all([walk(d0, maxAge), ...others.map(async t => walk(await get(t.ctx, maxAge), maxAge))]);
        return done.every(Boolean) ? 'complete' : 'partial';
    };
    let status = await crawl(0);
    if (status !== 'failed' && ![...day.values()].some(it => !it.trailer) && newestReal && target > newestReal && days(newestReal, target) <= 14) status = await crawl(180000);
    return { status, items: [...day.values()], pages };
}
// 从【一个 danmu_api 实例】取某剧某集弹幕：搜索 → 同剧多平台(iqiyi/360/...)回退 → 返回 DPlayer 数组(空=该实例没取到)
async function fetchDanmakuFromInstance(base, token, title, ep, hints) {
    base = String(base).replace(/\/$/, '');
    const prefix = token ? `/${encodeURIComponent(token)}` : '';
    const nt = String(title || '').replace(/\s+/g, '').toLowerCase();
    // 搜索结果按【实例+剧名】缓存：不同实例的 episodeId 体系不同，key 必须带 base，否则串实例取到失效 id
    let animes;
    const skey = base + '||' + nt;
    const sc = danmakuSearchCache.get(skey);
    if (sc && sc.expiry > Date.now()) { animes = sc.animes; }
    else {
        const _s0 = Date.now();
        const alt0 = danmakuAltTitle.get(skey);
        const useAlt = alt0 && alt0.alt && alt0.expiry > Date.now();
        try {
            const sr = await axios.get(`${base}${prefix}/api/v2/search/episodes`, { params: { anime: useAlt ? alt0.alt : title }, timeout: 20000 });
            animes = (sr.data && sr.data.animes) || [];
            console.log(`[弹幕诊断] search "${useAlt ? alt0.alt : title}" @${base} → ${animes.length} animes (${Date.now() - _s0}ms)`);
        } catch (e) {
            // ECONNABORTED=超时, ECONNREFUSED=拒连, ETIMEDOUT=连不上, ENOTFOUND=DNS, 或 HTTP 4xx/5xx(被WAF/限流拦)
            console.warn(`[弹幕诊断] search "${title}" @${base} 失败: ${e.code || ''} ${e.response ? 'HTTP' + e.response.status : e.message} (${Date.now() - _s0}ms)`);
            throw e;
        }
        // 搜不到 → 换季号写法再搜(见 danmakuTitleVariants)。换写法的搜索出错只当没搜到;全都是正常返回的空 → 15 分钟内不再换写法
        if (!animes.length && !(alt0 && alt0.none && alt0.expiry > Date.now())) {
            const alts = useAlt ? [title] : danmakuTitleVariants(title);
            let clean = true;
            for (const alt of alts) {
                const _a0 = Date.now();
                try {
                    const sr = await axios.get(`${base}${prefix}/api/v2/search/episodes`, { params: { anime: alt }, timeout: 20000 });
                    animes = (sr.data && sr.data.animes) || [];
                    console.log(`[弹幕诊断] search "${alt}"(换写法) @${base} → ${animes.length} animes (${Date.now() - _a0}ms)`);
                } catch (e) { clean = false; console.warn(`[弹幕诊断] search "${alt}"(换写法) @${base} 失败: ${e.code || ''} ${e.response ? 'HTTP' + e.response.status : e.message}`); }
                if (animes.length) { if (alt !== title) danmakuAltTitle.set(skey, { alt, expiry: Date.now() + 3600e3 }); else danmakuAltTitle.delete(skey); break; }
            }
            if (!animes.length && clean && alts.length && !useAlt) danmakuAltTitle.set(skey, { none: true, expiry: Date.now() + 15 * 60e3 });
            if (danmakuAltTitle.size > 500) { const k = danmakuAltTitle.keys().next().value; if (k !== undefined) danmakuAltTitle.delete(k); }
        }
        // ⚠️ 空 animes 不写缓存:上游限流的瞬时空若被缓存(旧 TTL 3min),外层 3s 重试和后续请求全被空快照挡住,
        //    实测全丢窗口超 3 分钟(对抗审查实锤)。不缓存空,重试才是真重试。
        if (animes.length) {
            if (danmakuSearchCache.size >= 500) { const k = danmakuSearchCache.keys().next().value; if (k !== undefined) danmakuSearchCache.delete(k); }
            danmakuSearchCache.set(skey, { animes, expiry: Date.now() + DANMAKU_SEARCH_TTL });
        }
    }
    const singleInstance = /^(1|true|yes|on)$/i.test(String(process.env.DANMU_API_SINGLE_INSTANCE || '').trim());
    if (!singleInstance && animes.some(a => (a.episodes || []).length) && !animes.some(a => (a.episodes || []).some(e => e && e.url !== undefined))) danmakuWarnNoUrl(base);
    // 🏅 候选排序见 danmakuRankCandidates(分档 + 类型 + 年份 + 季号 + 平台)
    const { pool, bestTier, why } = danmakuRankCandidates(animes, title, hints);
    if (!pool.length) { console.log(`[弹幕诊断] "${title}" @${base}: ${animes.length} 个候选里没有可用的(${why})`); return []; }
    const platOf = s => { const m = String(s || '').match(/from\s+([a-z0-9]+)/i); return m ? m[1].toLowerCase() : ''; };
    const yearM = String(title).match(/(?:19|20)\d{2}/);
    // 跨年同月日消歧(回看旧季不误取新季):剧名里的年份优先,没有就用资源站年份
    const preferYear = yearM ? yearM[0] : ((hints && Number(hints.year) > 1900) ? String(Number(hints.year)) : null);
    // 📅 腾讯综艺 + 日期式集名 + 前端给了时长:以腾讯为准(见 danmakuAirDatePick)。腾讯说不清(没有/不止一条对得上/没抓全/连不上)就没有,
    //   并告诉赛跑别的实例别按旧规则猜(_veto,见 danmakuRaceVerdict;对抗审查:aiyifan/360 这样猜,同一天几条里常挑错)。
    //   这个实例的候选里没有腾讯地址时,用别的实例认出过的 cid(danmakuQqCidMemo)。
    const ourDur = (hints && Number(hints.dur)) || 0;
    const airTarget = ourDur > 0 ? danmakuAirDateTarget(ep, preferYear) : '';
    const urlUnsupported = () => { const t = danmakuUrlMode.get(base); return !!t && Date.now() - t < 3600e3; };
    let cid = '';
    if (airTarget && !urlUnsupported()) {
        cid = danmakuPoolQqCid(pool);
        const mk = nt + '|' + (preferYear || '');
        if (cid) {
            if (danmakuQqCidMemo.size >= 500) { const k = danmakuQqCidMemo.keys().next().value; if (k !== undefined) danmakuQqCidMemo.delete(k); }
            danmakuQqCidMemo.set(mk, { cid, expiry: Date.now() + 24 * 3600e3 });
        } else { const m = danmakuQqCidMemo.get(mk); if (m && m.expiry > Date.now()) cid = m.cid; }
    }
    if (cid) {
        const day = await danmakuQqDay(cid, airTarget, Date.now() + (process.env.VERCEL ? 2500 : 8000));
        const it = day.status === 'complete' ? danmakuAirDatePick(day.items, ep, preferYear, ourDur) : null;
        console.log(`[弹幕诊断] 腾讯 ${cid} ${airTarget} 时长${ourDur}s: ${day.status}(${day.pages} 页) 当天 ${day.items.length} 条 → ${it ? it.title.slice(0, 24) + '(' + it.dur + 's)' : '认不出,不给'}`);
        if (!it) return danmakuVetoed();
        const url = `https://v.qq.com/x/cover/${cid}/${it.vid}.html`;
        const _q0 = Date.now();
        try {
            // 只这一条可取(不会退回别的候选),给足时间:danmu_api 冷抓几万条的腾讯弹幕要十几秒(实测 4 万条 >12s);Vercel 函数 10 秒封顶
            const cr = await axios.get(`${base}${prefix}/api/v2/comment`, { params: { url, chConvert: '0', format: 'json' }, timeout: process.env.VERCEL ? 7000 : 25000 });
            if (!cr.data || !Array.isArray(cr.data.comments)) throw new Error('bad body');
            const d = dandanToDplayer(cr.data.comments);
            console.log(`[弹幕诊断] comment(url) ${url} (腾讯发布日期) → ${d.length} 条 (${Date.now() - _q0}ms)`);
            if (!d.length) return danmakuVetoed();
            d._tier = Math.min(bestTier, 1);
            d._oracle = true;
            d._src = danmakuSourceOf({ url });
            return d;
        } catch (e) {
            const st = e.response && e.response.status;
            if (st === 429) danmakuWarnRateLimited(base);
            console.warn(`[弹幕诊断] comment?url(腾讯发布日期) 失败: ${e.code || ''} ${st ? 'HTTP' + st : e.message} (${Date.now() - _q0}ms)`);
            return danmakuVetoed();
        }
    }
    // 前面的候选取弹幕【瞬时失败】(超时/限流/5xx)后由后面的候选顶上:多半是弹幕少得多的别的平台(实测腾讯 4 万条超时 → aiyifan 309 条),
    //   照常长缓存 7 天就一直是那几百条 → 这种结果降为低置信(只短缓存),过会儿重抓能拿到正主的
    let transient = false;
    // ⏱️ 取弹幕的超时:优酷弹幕是 danmu_api 现抓的(一集分好几段翻页,它自己不缓存),实测《嫁金钗》一集 1.8 万条单抓 19~23 秒、
    //    两个实例同时抓同一集 32~33 秒、同时抓几集 21~38 秒。旧的一律 12 秒 → 每次都超时拿到空,空的又不进缓存,这部剧哪一集都没弹幕(2026-11 用户反馈)。
    //    VPS 一次最多等 55 秒,这个实例的几个候选合起来 60 秒封顶;前端不干等:端点到点先回"还在加载",抓完存进缓存,前端过两秒再要。
    //    Vercel 函数 10 秒封顶,照旧 12 秒。
    const cEnd = Date.now() + 60000;
    const cWait = () => process.env.VERCEL ? 12000 : Math.min(55000, cEnd - Date.now());
    for (let tries = 0; tries < pool.length && tries < 3; tries++) {
        if (cWait() < 5000) { transient = true; break; }
        const episode = pickDanmakuEpisode(pool[tries].episodes, ep, preferYear);
        if (!episode || (!episode.episodeId && !episode.url)) continue;
        const _c0 = Date.now();
        // 🔑 优先按【视频地址】取弹幕(comment?url=,无状态)。comment/<episodeId> 的 id 是 danmu_api【单个实例内存里】的自增号
        //    (globals.episodeNum):部署在 CF Workers 等多实例上、或重启后,搜索落在实例 A、取弹幕落在实例 B,同一个号在 B 上
        //    指向 B 最近搜过的别的剧 —— 真实回放实锤:三国演义拿到鬼灭之刃、庆余年第二季拿到刑侦剧、红楼梦拿到海贼王……
        //    再被我们长缓存 7 天。按地址取没有这个问题;老版本 danmu_api 不认 ?url= 时才退回按 id,且按 id 的结果一律当低置信(只短缓存)。
        //    按地址取只交给 danmu_api 的 getCommentByUrl 能处理的地址:http(s)(番组计划 bgm.tv / 巴哈 ani.gamer 的集地址它只在按 id 时特殊处理)
        //    与 local:。合并源("tencent:…<分隔>iqiyi:…")、renren:123 这类非 http 地址只能按 id。
        const rawUrl = String(episode.url || '');
        const url = (/^local:/.test(rawUrl) || (/^https?:\/\//i.test(rawUrl) && !/bgm\.tv|bangumi\.tv|ani\.gamer\.com\.tw/i.test(rawUrl))) ? rawUrl : '';
        let d = null, via = '';
        // "这个 danmu_api 不认 ?url="的时间见上面 urlUnsupported;1 小时后再试一次(站长升级了 danmu_api 不用重启本站)
        if (url && !urlUnsupported()) {
            try {
                const cr = await axios.get(`${base}${prefix}/api/v2/comment`, { params: { url, chConvert: '0', format: 'json' }, timeout: cWait() });
                if (!cr.data || !Array.isArray(cr.data.comments)) throw new Error('bad body');
                d = dandanToDplayer(cr.data.comments);
                via = 'url';
                danmakuUrlMode.delete(base);
            } catch (e) {
                const st = e.response && e.response.status;
                // 只有"这个 danmu_api 根本不认 ?url="(老版本:404,或 400 缺参数)才记下、以后对它改走按 id;
                //   429/5xx/超时/网络错 是这一次失败 —— 跳过这个候选,绝不退回按 id(按 id 正是多实例串剧的那条路,审查实锤)
                const body = e.response && e.response.data;
                if (st === 404 || (st === 400 && /missing|commentid|url/i.test(JSON.stringify(body || '')))) danmakuUrlMode.set(base, Date.now());
                if (st === 429) danmakuWarnRateLimited(base);
                console.warn(`[弹幕诊断] comment?url(${platOf(pool[tries].animeTitle) || '?'}) 失败: ${e.code || ''} ${st ? 'HTTP' + st : e.message} (${Date.now() - _c0}ms)`);
                if (!urlUnsupported()) { transient = true; continue; }
            }
        }
        // 按 id:只在 ①这个 danmu_api 不支持按地址取,或 ②这一集没有可按地址取的地址 且 站长声明 danmu_api 是单实例(DANMU_API_SINGLE_INSTANCE=1)时才用。
        //   多实例上按 id 会串到别的剧,所以按 id 的结果一律低置信、不缓存(见端点 viaId)。
        const idAllowed = urlUnsupported() || (!url && singleInstance);
        if (d === null && episode.episodeId && idAllowed) {
            try {
                const cr = await axios.get(`${base}${prefix}/api/v2/comment/${episode.episodeId}`, { params: { withRelated: 'true', chConvert: '0' }, timeout: cWait() });
                d = dandanToDplayer((cr.data && cr.data.comments) || []);
                via = 'id';
            } catch (e) {
                transient = true;
                if (e.response && e.response.status === 429) danmakuWarnRateLimited(base);
                console.warn(`[弹幕诊断] comment/${episode.episodeId} 失败: ${e.code || ''} ${e.response ? 'HTTP' + e.response.status : e.message} (${Date.now() - _c0}ms)`);
            }
        }
        if (d === null) continue;
        console.log(`[弹幕诊断] comment(${via}) ${via === 'url' ? url : episode.episodeId} (${platOf(pool[tries].animeTitle) || '?'}) 《${pool[tries].animeTitle}》 ${why} → ${d.length} 条 (${Date.now() - _c0}ms)`);
        // _tier 供端点分级缓存:包含档、以及按 id 取到的(可能串到别的剧)都不给长缓存、不进持久层
        // _src:实际取到这份弹幕的候选的平台(前面的候选失败、后面顶上时也跟着变);按 id 取的可能串到别的剧,不算数
        if (d.length) { d._tier = (via === 'url' && !transient) ? bestTier : Math.max(bestTier, 2); if (via === 'id') d._viaId = true; else d._src = danmakuSourceOf(episode); return d; }
    }
    return transient ? danmakuFailed() : [];
}
app.get('/api/danmaku/v3/', async (req, res) => {
    const empty = { code: 0, version: 3, data: [], msg: '' };
    // 缓存策略：空/出错一律 no-store——绝不让 CDN/浏览器缓存"暂时为空"的弹幕。
    //   (事故：CF 的"浏览器缓存TTL=1年"会把空响应在每个用户浏览器冻结一年 → 某集偶发一次取空就永久没弹幕。
    //    服务器侧另有 90s miss 缓存护住上游，所以 no-store 不会反复打 danmu_api。)
    // 取到非空弹幕才长缓存：弹幕近乎静态 → 7 天新鲜 + 30 天 stale-while-revalidate(过期先回旧缓存秒开、后台重抓)。
    //   服务器自己也按同样的口径长存(danmakuStore:SQLite 持久,DANMAKU_CACHE_DAYS 天新鲜,默认 7)。
    // 注意：缓存键 = ?id=剧名|集名(稳定)；不要去缓存 danmu_api 的 comment/{id}(id 会过期、键永远变)。
    const LONG_CACHE = 'public, max-age=604800, s-maxage=604800, stale-while-revalidate=2592000';
    res.set('Cache-Control', 'no-store');
    const DANMU_API_URL = process.env.DANMU_API_URL;
    if (!DANMU_API_URL) return res.json(empty);

    // id = 剧名|集名|版本[|k:类型|t:资源站分类|y:年份|n:集数](解析与缓存键见 danmakuParseId,两后端共用)
    const { title, ep, hints, cacheKey } = danmakuParseId(req.query.id);
    if (!title) return res.json(empty);

    const storeKey = DANMAKU_STORE_VER + '|' + cacheKey;
    // ① 服务器长缓存(高贴合非空):新鲜期内直接回;过期了也先回旧的(秒开),同时后台重抓一次——
    //    重抓拿到空/低置信不覆盖旧的(上游瞬时空不能冲掉好弹幕),一小时内不再重试这一集。
    const hit = danmakuStore.get(storeKey);
    if (hit) {
        // 🏷️ 老条目(加来源字段之前存的,没有 src):弹幕照常回,前端按未知来源、不校正。不作废,只是把下一次后台重抓提前,抓到才替换,抓不到还用旧的;
        //    这期间只给 10 分钟缓存头,免得 CDN / 浏览器把"没来源"的版本再钉 7 天。提前重抓限速,不挤占前台回源配额(见 danmakuUpgradeOk)
        const upgrade = hit.fresh && !hit.hasSrc;
        if ((!hit.fresh || upgrade) && danmakuStore.refreshAllowed(storeKey) && (!upgrade || danmakuUpgradeOk()) && danmakuBudgetOk()) {
            danmakuStore.once('bg|' + storeKey, async () => {
                const r = await fetchDanmakuFresh(title, ep, hints);
                if (r.data.length && !r.lowConf && !r.viaId) danmakuStore.put(storeKey, r.data, r.src);
                else danmakuStore.refreshFailed(storeKey);
            }).catch(() => danmakuStore.refreshFailed(storeKey));
        }
        res.set('Cache-Control', hit.hasSrc ? LONG_CACHE : 'public, max-age=600, s-maxage=600');
        return res.type('application/json').send(hit.json);
    }
    // ② 空 / 低置信结果的短期内存缓存(不落盘):低置信只给 CDN 10 分钟,空的 no-store
    //    空结果带上原因(why),前端据此提示:fail = 弹幕源出错 / 超时,busy = 本站回源配额用完;没有 why = 真没有(没配上 / 平台没弹幕)
    const cached = danmakuCache.get(cacheKey);
    if (cached && cached.expiry > Date.now()) {
        if (cached.data.length && !cached.viaId) res.set('Cache-Control', 'public, max-age=600, s-maxage=600');
        return res.json(Object.assign({ code: 0, version: 3, src: cached.src || '', data: cached.data, msg: '' }, cached.fail && !cached.data.length ? { why: 'fail' } : {}));
    }
    if (!danmakuBudgetOk()) return res.json(Object.assign({}, empty, { why: 'busy' }));

    try {
        // ③ 回源:同一集同时只打一次 danmu_api(热剧新集刚出,几十人同时点开也只抓一次)
        const job = danmakuStore.once(storeKey, async () => {
            const r = await fetchDanmakuFresh(title, ep, hints);
            if (r.data.length && !r.lowConf && !r.viaId) return { json: danmakuStore.put(storeKey, r.data, r.src), long: true };
            if (danmakuCache.size >= DANMAKU_CACHE_MAX) { const k = danmakuCache.keys().next().value; if (k !== undefined) danmakuCache.delete(k); }
            danmakuCache.set(cacheKey, { data: r.data, lowConf: r.lowConf, viaId: r.viaId, src: r.src, fail: r.fail, expiry: Date.now() + (r.data.length && !r.viaId ? DANMAKU_LOWCONF_TTL : DANMAKU_MISS_TTL) });
            return { json: r.fail ? JSON.stringify(Object.assign({}, empty, { src: '', why: 'fail' })) : danmakuStore.toJson(r.data, r.src), long: false, n: r.viaId ? 0 : r.data.length };
        });
        // ⏳ 慢平台(优酷一集现抓 20~40 秒)前台最多等 DANMAKU_FG_WAIT:到点先回"还在加载"(pending,no-store),抓取在后台照常跑完、存进缓存;
        //    前端见 pending 两秒后再要 —— 同一集正在抓的会合并进这一次(danmakuStore.once),不重复回源
        let fgTimer = null;
        const out = await Promise.race([job, new Promise(r => { fgTimer = setTimeout(() => r(null), DANMAKU_FG_WAIT); })]);
        clearTimeout(fgTimer);
        if (!out) return res.json(Object.assign({}, empty, { pending: 1 }));
        if (out.long) res.set('Cache-Control', LONG_CACHE);
        else if (out.n) res.set('Cache-Control', 'public, max-age=600, s-maxage=600');
        return res.type('application/json').send(out.json);
    } catch (e) {
        console.error('[弹幕] 获取失败:', e.message);
        return res.json(empty);
    }
});
// 回源抓一集弹幕(多实例赛跑 + 全空重试 + 排序 + 采样)。返回 { data, lowConf }。
async function fetchDanmakuFresh(title, ep, hints) {
    // 多源回退：DANMU_API_URL 支持逗号分隔多个实例(不同主机/区域=不同出口IP,绕开单实例被上游限流)；
    //   DANMU_API_TOKEN 逗号分隔则按序与各实例配对，单个则全部实例共用。
    const bases = String(process.env.DANMU_API_URL || '').split(',').map(s => s.trim()).filter(Boolean);
    const tokens = String(process.env.DANMU_API_TOKEN || '').split(',').map(s => s.trim());
    const instances = bases.map((b, i) => ({ base: b, token: tokens.length > 1 ? (tokens[i] || '') : (tokens[0] || '') }));
    // 🏁 并行赛跑：所有实例同时查，第一个返回【高贴合(_tier≤1)非空】的立即采用——一个实例卡死/401 不再拖累其它。
    //    包含档(_tier≥2)结果不立即定音:压 1.5s 等高贴合结果到来——防"降级实例的杂牌错弹幕抢跑赢过健康实例的
    //    正主弹幕"(对抗审查实锤:多实例冗余反成投毒面)。1.5s 内没有更好的才用它。
    const dated = danmakuAirDated(title, ep, hints);
    const raceInstances = () => new Promise(resolve => {
        if (!instances.length) return resolve([]);
        let pending = instances.length, held = null, timer = null, done = false, veto = false, fail = false;
        const finish = v => { if (done) return; done = true; if (timer) clearTimeout(timer); resolve(v); };
        for (const inst of instances) {
            fetchDanmakuFromInstance(inst.base, inst.token, title, ep, hints)
                .then(d => {
                    if (d && d._fail) fail = true;
                    const v = danmakuRaceVerdict(d, dated);
                    if (v === 'veto') veto = true;
                    else if (v === 'finish') finish(d);
                    else if (v === 'holdAll') {
                        if (!held || (d._tier ?? 9) < (held._tier ?? 9)) held = d;
                        // 腾讯认集的实例可能还在路上(它的结论能否掉这条):最多再等 15s(Vercel 2.5s);等到点了这条只当低置信用
                        if (!timer) timer = setTimeout(() => { if (held) held._tier = Math.max(held._tier ?? 9, 2); finish(veto ? danmakuVetoed() : held); }, process.env.VERCEL ? 2500 : 15000);
                    }
                    else if (v === 'hold' && !held) { held = d; timer = setTimeout(() => finish(held), 1500); }
                })
                .catch(() => { fail = true; })
                .finally(() => { if (--pending === 0) finish(veto ? danmakuVetoed() : (held || (fail ? danmakuFailed() : []))); });
        }
    });
    // ⏱️ 总时限:单轮最多 85s(搜索 20s + 每个实例取弹幕合计 60s),超时按"这次没取到(出错)"处理。前台不等这么久(见端点 DANMAKU_FG_WAIT),
    //    这里只给后台抓取兜底
    const deadline = (p, ms) => new Promise(resolve => { const t = setTimeout(() => resolve(danmakuFailed()), ms); p.then(v => { clearTimeout(t); resolve(v); }); });
    const t0 = Date.now();
    let data = await deadline(raceInstances(), 85000);
    // 全空 → 多为上游(iqiyi)限流的瞬时空(实测同集隔几秒重试即满)：等 3s 再赛一轮。
    //   (搜索级空快照已不再缓存,这轮重试会真正重新搜索。)
    //   超出集数时 pickDanmakuEpisode 返回 null → 各实例本就返回空、这里也取不到，保持空。
    //   只在第一轮【很快】就空了时重试:第一轮是超时 / 慢平台没抓完的,马上再抓一遍一样慢,白占上游(旧版《嫁金钗》两轮各超时一次)
    if (!data.length && !data._veto && instances.length && Date.now() - t0 < 15000) {
        await new Promise(r => setTimeout(r, 3000));
        data = await deadline(raceInstances(), 85000);
    }
    const fail = !data.length && !!data._fail;
    // 包含档(杂牌名字沾边)结果置信低:服务器只缓存 10 分钟、CDN/浏览器只给 10 分钟——错了也只错一阵,
    // 不再被 7 天 LONG_CACHE 固化(对抗审查实锤:史莱姆事故的错弹幕曾三层缓存一周)。
    const lowConf = !!(data && data.length && (data._tier ?? 9) >= 2);
    const viaId = !!(data && data._viaId);   // 按 id 取的(多实例上可能是别的剧):端点一律 no-store、只在内存放 90 秒
    // 🏷️ 平台来源:要在下面采样(换数组)之前读;低置信 / 按 id 的可能根本不是这部剧,来源不作数
    const src = (data && data.length && !lowConf && !viaId) ? String(data._src || '') : '';
    // 上游不保证按时间排序：先按时间[0]升序，确保下面"按索引均匀采样"=="按时间均匀采样"(后半段不丢)
    data.sort((a, b) => a[0] - b[0]);
    // 热门剧单集可达 1.5w+ 条(payload~1.5MB)：按时间均匀采样到上限，控制体积与前端渲染压力
    if (data.length > DANMAKU_MAX) { const step = data.length / DANMAKU_MAX, s = []; for (let i = 0; i < DANMAKU_MAX; i++) s.push(data[Math.floor(i * step)]); data = s; }
    return { data, lowConf, viaId, src, fail };
}
// 🏷️ 老条目补来源的提前重抓:每分钟最多 30 集。全站回源配额(danmakuBudgetOk,300 次/分钟)用完前台新集会直接拿到空弹幕,发版后第一波不能把它吃光
let danmakuUpgWinStart = 0, danmakuUpgWinCount = 0;
function danmakuUpgradeOk() {
    const now = Date.now();
    if (now - danmakuUpgWinStart > 60000) { danmakuUpgWinStart = now; danmakuUpgWinCount = 0; }
    if (danmakuUpgWinCount >= 30) return false;
    danmakuUpgWinCount++;
    return true;
}
// 借来的弹幕只读：DPlayer 发送弹幕会 POST 到此，直接成功返回不持久化(避免报错)
app.post('/api/danmaku/v3/', (req, res) => res.json({ code: 0, msg: '' }));

// 2. 搜索 API - SSE 流式版本 (GET, 用于实时搜索)
// 支持智能多关键词搜索：自动生成关键词变体提高搜索命中率
app.get('/api/search', async (req, res) => {
    const keyword = req.query.wd;
    const originalTitle = req.query.original || '';  // 可选：原始标题（如英文名）
    const stream = req.query.stream === 'true';
    const smartSearch = req.query.smart !== 'false';  // 默认启用智能搜索

    if (!keyword) {
        return res.status(400).json({ error: 'Missing keyword' });
    }

    // 🔥 热词统计：用户发起任一搜索(无论命中缓存/站内多站点)均计热一次。放在缓存 miss/set 更准——
    //    否则同一词命中缓存后不再计次, 热度永远起不来。
    recordSearchTerm(keyword);

    const sites = allSites();
    const includeNsfw = truthyFlag(req.query.include_nsfw);

    if (!stream) {
        // 非流式模式：返回聚合的 JSON 结果（用于 refreshEpisodes 查找 vod_id）
        const siteKey = req.query.site_key;  // 可选：只搜索指定站点
        // 指定 site_key 时按原站点查（刷新集数/线路）；全站搜索才受成人过滤控制
        const targetSites = siteKey
            ? sites.filter(s => s.key === siteKey)
            : (includeNsfw ? sites : sites.filter(s => !isNsfwSite(s)));

        const allResults = [];
        // ⚖️ 非流式(直达用)同样健康源优先：加快 playRecommendation 等路径在 8s 边界内拿到优质源
        const targetRanked = [...targetSites].sort((a, b) => siteHealthScore(b.key) - siteHealthScore(a.key));
        const searchPromises = targetRanked.map(async (site) => {
            const site_profile = profOf(site);   // 🏷️ 发出时才附加:不进 1 小时搜索缓存,改 db.json 覆盖/档案表立即生效
            if (kazumi && kazumi.isKzSite(site)) {   // 🎌 规则站:模块自带关键词策略与缓存
                try {
                    const r = await kazumi.search(site.key, keyword, originalTitle);
                    ((r && r.list) || []).forEach(item => allResults.push({ ...item, site_key: site.key, site_name: site.name, site_profile }));
                } catch (err) { console.error(`[Search JSON] ${site.name}:`, err.message); }
                return;
            }
            const cacheKey = `${site.key}_${keyword}`;
            const cached = cacheManager.get('search', cacheKey);
            if (cached && cached.list) {
                recordSiteHealth(site.key, true);
                cached.list.forEach(item => {
                    allResults.push({ ...item, site_key: site.key, site_name: site.name, site_profile });
                });
                return;
            }
            try {
                if (isExtSite(site)) {
                    // XPTV js 扩展源: 调用 search()
                    const extList = await extSearch(site, keyword);
                    recordSiteHealth(site.key, true);
                    cacheManager.set('search', cacheKey, { list: extList }, searchTTL(keyword));
                    allResults.push(...(extList.map(item => ({ ...item, site_key: site.key, site_name: site.name }))));
                    return;
                }
                const searchUrl = `${site.api}?ac=detail&wd=${encodeURIComponent(keyword)}`;
                const { data } = await fetchWithProxyFallback(searchUrl, { timeout: 8000 }, site.key);
                const list = data.list ? data.list.map(item => ({
                    vod_id: item.vod_id,
                    vod_name: item.vod_name,
                    vod_pic: item.vod_pic,
                    vod_year: item.vod_year,   // 刷新线路后 Kazumi 源的年份校验要用
                    type_name: item.type_name, // 刷新线路后弹幕匹配提示(分类)要用
                    vod_play_url: item.vod_play_url,
                    site_key: site.key,
                    site_name: site.name
                })) : [];
                recordSiteHealth(site.key, true);
                cacheManager.set('search', cacheKey, { list }, searchTTL(keyword));
                allResults.push(...list.map(item => ({ ...item, site_profile })));   // 缓存里的 list 保持不带档案
            } catch (err) {
                recordSiteHealth(site.key, false);
                console.error(`[Search JSON] ${site.name}:`, err.message);
            }
        });
        // ⏱ 非流式搜索上限 8s：多数源本地已有缓存或响应快，最快几秒即可返回；
        //    个别坏源/慢源(extSearch 最长 25s)不拖垮整个请求——8s 后会返回目前已收集到的结果。
        //    这让 playRecommendation/继续播放的"直达播放"在 12s 边界内能拿到数据，而不是整体超时回退。
        await Promise.race([
            Promise.all(searchPromises),
            new Promise(resolve => setTimeout(resolve, 8000))
        ]);
        return res.json({ list: allResults });
    }

    // SSE 流式模式
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache');
    res.setHeader('Connection', 'keep-alive');
    res.setHeader('X-Accel-Buffering', 'no'); // 禁用 Nginx 缓冲

    // 生成搜索关键词变体
    let searchKeywords = smartSearch
        ? generateSearchKeywords(keyword, originalTitle)
        : [keyword];

    // 智能翻译：如果关键词是英文，尝试通过 TMDB 获取中文名
    if (smartSearch && isMainlyEnglish(keyword)) {
        console.log(`[Smart Search] 检测到英文关键词，尝试获取中文翻译: ${keyword}`);
        const chineseTitles = await fetchChineseTitleFromTMDB(keyword);
        if (chineseTitles.length > 0) {
            // 将中文标题加入搜索列表，并对中文标题也生成变体
            for (const cn of chineseTitles) {
                const cnVariants = generateSearchKeywords(cn);
                for (const v of cnVariants) {
                    if (!searchKeywords.includes(v)) {
                        searchKeywords.push(v);
                    }
                }
            }
        }
    }

    if (searchKeywords.length > 1) {
        console.log(`[Smart Search] 生成关键词变体: ${searchKeywords.join(' | ')}`);
    }

    // 用于跟踪已发送的结果，避免重复
    const sentVodIds = new Map(); // key: site_key_vod_id, value: true

    // 并行搜索所有站点（关闭成人过滤时才包含黄果等 NSFW 扩展源）
    const searchSites = includeNsfw ? sites : sites.filter(s => !isNsfwSite(s));
    // ⚖️ 健康源优先：按历史健康度从高到低排序，健康源先请求先返回，坏源压到后面，
    //    让"快速命中即播"(quickPlay/继续播放)更快拿到优质源，而不是先被慢/坏源拖住。
    const rankedSites = [...searchSites].sort((a, b) => siteHealthScore(b.key) - siteHealthScore(a.key));
    const searchPromises = rankedSites.map(async (site) => {
        const site_profile = profOf(site);   // 🏷️ 发出时才附加,不写进搜索缓存
        // 🎌 规则站(HTML 刮削的小站):对空格敏感、七色番 wd 只取前 10 字,智能变体对它们全是无效请求还徒增被封风险
        //    → 交给模块:一个"核心关键词",0 结果才回退一次;结果带 _gk 等归一化键供前端并组
        if (kazumi && kazumi.isKzSite(site)) {
            let list = [];
            try { list = ((await kazumi.search(site.key, keyword, originalTitle)) || {}).list || []; }
            catch (error) { console.error(`[SSE Search Error] ${site.name}:`, error.message); }
            const items = list.map(item => ({ ...item, site_key: site.key, site_name: site.name, site_profile })).filter(item => {
                const globalKey = `${item.site_key}_${item.vod_id}`;
                if (sentVodIds.has(globalKey)) return false;
                sentVodIds.set(globalKey, true);
                return true;
            });
            if (items.length > 0) res.write(`data: ${JSON.stringify(items)}\n\n`);
            return items;
        }
        // 对每个站点，尝试所有关键词变体
        const allResults = [];

        for (const kw of searchKeywords) {
            const cacheKey = `${site.key}_${kw}`;
            const cached = cacheManager.get('search', cacheKey);

            if (cached && cached.list) {
                // 命中缓存
                recordSiteHealth(site.key, true);
                allResults.push(...cached.list);
            } else {
                try {
                    // 只在第一个关键词时打印日志，避免日志刷屏
                    if (kw === searchKeywords[0]) {
                        console.log(`[SSE Search] ${site.name} -> ${searchKeywords.length > 1 ? searchKeywords.join(' | ') : kw}`);
                    }

                    // 构建请求 URL（带参数）
                    const searchUrl = `${site.api}?ac=detail&wd=${encodeURIComponent(kw)}`;

                    // 使用带代理回退的请求
                    let list = [];
                    if (isExtSite(site)) {
                        // XPTV js 扩展源: 调用 search()
                        const extList = await extSearch(site, kw);
                        list = extList;
                    } else {
                        const { data, usedProxy } = await fetchWithProxyFallback(searchUrl, { timeout: 8000 }, site.key);

                        if (usedProxy && kw === searchKeywords[0]) {
                            console.log(`[SSE Search] ${site.name} 通过代理获取结果`);
                        }

                        list = data.list ? data.list.map(item => ({
                            vod_id: item.vod_id,
                            vod_name: item.vod_name,
                            vod_pic: item.vod_pic,
                            vod_remarks: item.vod_remarks,
                            vod_year: item.vod_year,
                            type_name: item.type_name,
                            vod_content: item.vod_content,
                            vod_play_from: item.vod_play_from,
                            vod_play_url: item.vod_play_url
                        })) : [];
                    }

                    // 有结果记健康成功(哪怕0条也算连接成功)；无结果本轮可视为成功连接
                    recordSiteHealth(site.key, true);

                    // 缓存结果 (热词翻倍 TTL)
                    cacheManager.set('search', cacheKey, { list }, searchTTL(kw));

                    allResults.push(...list);
                } catch (error) {
                    recordSiteHealth(site.key, false); // 搜索失败 = 该源当前不健康
                    // 单个关键词失败不影响其他
                    if (kw === searchKeywords[0]) {
                        console.error(`[SSE Search Error] ${site.name}:`, error.message);
                    }
                }
            }
        }

        // 对该站点的结果去重（基于 vod_id）
        const uniqueResults = [];
        const seenIds = new Set();

        for (const item of allResults) {
            if (!seenIds.has(item.vod_id)) {
                seenIds.add(item.vod_id);
                uniqueResults.push({
                    ...item,
                    site_key: site.key,
                    site_name: site.name,
                    site_profile
                });
            }
        }

        // 发送结果到客户端（检查全局去重）
        const newItems = uniqueResults.filter(item => {
            const globalKey = `${item.site_key}_${item.vod_id}`;
            if (!sentVodIds.has(globalKey)) {
                sentVodIds.set(globalKey, true);
                return true;
            }
            return false;
        });

        if (newItems.length > 0) {
            res.write(`data: ${JSON.stringify(newItems)}\n\n`);
        }

        return newItems;
    });

    // 等待所有搜索完成
    await Promise.all(searchPromises);

    // 发送完成事件
    res.write('event: done\ndata: {}\n\n');
    res.end();
});


// 2b. 搜索 API - POST 版本 (用于单站点搜索)
app.post('/api/search', async (req, res) => {
    const { keyword, siteKey } = req.body;
    const sites = allSites();
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });
    if (kazumi && kazumi.isKzSite(site)) {
        try { return res.json(await kazumi.search(site.key, keyword, '')); }
        catch (error) { console.error(`[Search Error] ${site.name}:`, error.message); return res.status(500).json({ error: 'Search failed' }); }
    }

    const cacheKey = `${siteKey}_${keyword}`;
    const cached = cacheManager.get('search', cacheKey);
    if (cached) {
        console.log(`[Cache] Hit search: ${cacheKey}`);
        return res.json(cached);
    }

    try {
        console.log(`[Search] ${site.name} -> ${keyword}`);

        // XPTV js 扩展源支持
        if (isExtSite(site)) {
            const extList = await extSearch(site, keyword);
            const result = { list: extList };
            cacheManager.set('search', cacheKey, result, searchTTL(keyword));
            return res.json(result);
        }

        // 构建请求 URL
        const searchUrl = `${site.api}?ac=detail&wd=${encodeURIComponent(keyword)}`;
        const { data } = await fetchWithProxyFallback(searchUrl, { timeout: 8000 }, site.key);

        // 简单的数据清洗
        const result = {
            list: data.list ? data.list.map(item => ({
                vod_id: item.vod_id,
                vod_name: item.vod_name,
                vod_pic: item.vod_pic,
                vod_remarks: item.vod_remarks,
                vod_year: item.vod_year,
                type_name: item.type_name
            })) : []
        };

        cacheManager.set('search', cacheKey, result, searchTTL(keyword)); // 热词翻倍 TTL
        res.json(result);
    } catch (error) {
        console.error(`[Search Error] ${site.name}:`, error.message);
        res.status(500).json({ error: 'Search failed' });
    }
});

// 3. 详情 API (带缓存) - GET 版本
app.get('/api/detail', async (req, res) => {
    const id = req.query.id;
    const siteKey = req.query.site_key;
    const requestedName = String(req.query.name || '').trim();
    const requestedPic = String(req.query.pic || '').trim();
    const nocache = req.query.nocache === '1';
    const sites = allSites();
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });
    if (kazumi && kazumi.isKzSite(site)) {   // 🎌 规则站:模块抓详情页、拼 maccms 形状的 vod_play_url(选集=/api/kz/ep/…)
        try {
            const r = await kazumi.detail(site.key, id, { fresh: nocache });
            if (r && r.list && r.list.length) return res.json({ list: [r.list[0]] });
            return res.status(404).json({ error: 'Not found', list: [] });
        } catch (error) {
            console.error(`[Detail Error] ${site.name}:`, error.message);
            return res.status(500).json({ error: 'Detail fetch failed', list: [] });
        }
    }

    const cacheKey = `${siteKey}_detail_${id}`;
    if (!nocache) {
        const cached = cacheManager.get('detail', cacheKey);
        if (cached) {
            console.log(`[Cache] Hit detail: ${cacheKey}`);
            // 返回格式：{ list: [detail] }，与前端期望一致
            return res.json({ list: [cached] });
        }
    } else {
        console.log(`[Detail] nocache=1, 跳过缓存: ${cacheKey}`);
    }

    try {
        console.log(`[Detail] ${site.name} -> ID: ${id}`);

        if (isExtSite(site)) {
            // XPTV js 扩展源: 优先从缓存获取剧集架构；未命中时并行拉取目录 + 第1集直链，实现极限提速
            const tracksCacheKey = `ext_tracks_${site.key}_${id}`;
            // 普通打开复用 30 分钟目录缓存；用户主动刷新时真正绕过该缓存。
            let extR = nocache ? null : cacheManager.get('detail', tracksCacheKey);
            let preResolvedPi = null;

            if (!extR) {
                let trackUrl = id.startsWith('http') ? id : undefined;
                if (!trackUrl && req.query.url) trackUrl = String(req.query.url);
                if (!trackUrl && site.key === 'age') trackUrl = `https://api.agedm.io/v2/detail/${id}`;
                if (!trackUrl && site.key === 'kuaikaw') trackUrl = `https://www.kuaikaw.cn/drama/${id}`;
                if (!trackUrl && site.key === 'ppnix') trackUrl = `https://www.ppnix.com/cn/movie/${id}.html`;
                const trackArg = { id: id, url: trackUrl };
                const defaultEp1Url = site.key === 'huangguo' ? `https://huangguoai.com/video/${id}/` : null;
                const [fetchedTracks, fetchedPi] = await Promise.all([
                    runExtJs(site, 'getTracks', trackArg).catch(() => null),
                    (defaultEp1Url && !getCachedExtPlayinfo(defaultEp1Url))
                        ? runExtJs(site, 'getPlayinfo', { url: defaultEp1Url, ep: '1' }).catch(() => null)
                        : Promise.resolve(null)
                ]);
                extR = fetchedTracks;
                preResolvedPi = fetchedPi;
                if (extR && (extR.list || extR.tracks)) {
                    cacheManager.set('detail', tracksCacheKey, extR, 1800);
                }
            }

            const groups = (extR && (extR.list || (extR.tracks ? [extR] : []))) || [];
            if (groups.length > 0) {
                const first = groups[0];
                const tracks = first.tracks || first.list || [];
                let vod_play_url = '';
                let playFrom = first.title || site.name;

                if (tracks.length > 0) {
                    const firstTrack = tracks[0];
                    const basePageUrl = String(req.query.url || '') || EXT_BASE_HOSTS[String(site.key || '').toLowerCase()] || '';
                    let firstUrl = absoluteExtUrl(firstTrack?.ext?.url || firstTrack?.url || firstTrack?.ext?.play_url || '', basePageUrl);
                    if (firstUrl && !firstUrl.includes('.m3u8') && !firstUrl.includes('.mp4')) {
                        const cached = getCachedExtPlayinfo(firstUrl);
                        if (cached) {
                            firstUrl = cached;
                        } else if (preResolvedPi) {
                            const resolved = extPlayinfoToVodUrl(preResolvedPi);
                            if (resolved && (resolved.includes('.m3u8') || resolved.includes('.mp4'))) {
                                setCachedExtPlayinfo(firstUrl, resolved);
                                firstUrl = resolved;
                            }
                        } else {
                            try {
                                const piArg = { url: firstUrl, ep: firstTrack.name || '1' };
                                const pi = await runExtJs(site, 'getPlayinfo', piArg);
                                const resolved = extPlayinfoToVodUrl(pi);
                                if (resolved && (resolved.includes('.m3u8') || resolved.includes('.mp4'))) {
                                    setCachedExtPlayinfo(firstUrl, resolved);
                                    firstUrl = resolved;
                                }
                            } catch (e) { }
                        }
                    }

                    // 相对 URL 补全为绝对地址：部分源（如 lmm85）返回 "/play/xxx.html"，
                    // 用 source 详情页 URL 作为基准拼接（basePageUrl 已在上面声明）。
                    const absoluteUrl = u => absoluteExtUrl(u, basePageUrl);
                    vod_play_url = tracks.map((t, index) => {
                        const epName = t.name || '第' + (index + 1) + '集';
                        const epUrl = index === 0 ? firstUrl : absoluteUrl(t.ext?.url || t.url || t.ext?.play_url || '');
                        return `${epName}$${epUrl}`;
                    }).join('#');

                    // 后台并行预解析后续最多 10 集（控制在途并发 4），
                    // 点击任意后续集/自动连播直接命中缓存，不再现场冷解析。
                    const warmTracks = tracks.slice(1, 12).filter(t => {
                        const u = t?.ext?.url || t?.url || '';
                        return u && !u.includes('.m3u8') && !u.includes('.mp4') && !getCachedExtPlayinfo(u);
                    });
                    if (warmTracks.length > 0) {
                        setImmediate(() => {
                            let wi = 0;
                            const CONC = 4;
                            const worker = async () => {
                                while (wi < warmTracks.length) {
                                    const t = warmTracks[wi++];
                                    const u = t?.ext?.url || t?.url || '';
                                    try {
                                        const r = await resolveExtMediaUrl(site, u, t.ext || { ep: t.name || String(wi) });
                                        if (r && r.url) warmExtManifest(String(site.key || ''), r.url);
                                    } catch (e) { }
                                }
                            };
                            Promise.allSettled([1, 1, 1, 1].map(worker));
                        });
                    }

                    // 首集媒体直链确定后，后台顺手把 m3u8 清单也预热进缓存：
                    // 用户点开详情直接点播放时，/api/ext-hls-proxy 直接命中缓存，省一次上游清单请求。
                    warmExtManifest(String(site.key || ''), firstUrl);
                    // 同时预热该剧“下一集”的清单（连播时首段不冷）。
                    if (tracks[1] && firstUrl && /\.m3u8/i.test(firstUrl)) {
                        const nxt = tracks[1]?.ext?.url || tracks[1]?.url || '';
                        warmExtManifest(String(site.key || ''), nxt);
                    }
                }

                const detail = {
                    vod_id: String(id),
                    vod_name: requestedName || extR.title || first.title || (site.name + ' - ' + id),
                    vod_pic: requestedPic || extR.pic || extR.cover || '',
                    vod_remarks: tracks.length ? tracks.length + ' 集' : (groups.length + ' 个剧组合集'),
                    vod_play_from: playFrom,
                    vod_play_url: vod_play_url,
                };
                return res.json({ list: [detail] });
            }
            return res.status(404).json({ error: 'Not found', list: [] });
        }

        // 构建请求 URL
        const detailUrl = `${site.api}?ac=detail&ids=${encodeURIComponent(id)}`;
        const { data } = await fetchWithProxyFallback(detailUrl, { timeout: 8000 }, site.key);

        if (data.list && data.list.length > 0) {
            const detail = data.list[0];
            cacheManager.set('detail', cacheKey, detail, 3600); // 缓存1小时
            // 返回格式：{ list: [detail] }，与前端期望一致
            res.json({ list: [detail] });
        } else {
            res.status(404).json({ error: 'Not found', list: [] });
        }
    } catch (error) {
        console.error(`[Detail Error] ${site.name}:`, error.message);
        res.status(500).json({ error: 'Detail fetch failed', list: [] });
    }
});

// 3b. 详情 API (带缓存) - POST 版本
app.post('/api/detail', async (req, res) => {
    const { id, siteKey } = req.body;
    const sites = allSites();
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });
    if (kazumi && kazumi.isKzSite(site)) {
        try {
            const r = await kazumi.detail(site.key, id);
            if (r && r.list && r.list.length) return res.json(r.list[0]);
            return res.status(404).json({ error: 'Not found' });
        } catch (error) { console.error(`[Detail Error] ${site.name}:`, error.message); return res.status(500).json({ error: 'Detail fetch failed' }); }
    }

    const cacheKey = `${siteKey}_detail_${id}`;
    const cached = cacheManager.get('detail', cacheKey);
    if (cached) {
        console.log(`[Cache] Hit detail: ${cacheKey}`);
        return res.json(cached);
    }

    try {
        console.log(`[Detail] ${site.name} -> ID: ${id}`);

        // XPTV js 扩展源支持: getTracks 拿剧集
        if (isExtSite(site)) {
            const extR = await runExtJs(site, 'getTracks', { id });
            const groups = (extR && extR.list) || [];
            if (groups.length > 0) {
                const first = groups[0];
                const tracks = first.tracks || [];
                let vod_play_url = extTracksToPlayUrl(tracks);
                const detail = {
                    vod_id: String(id),
                    vod_name: first.title || site.name,
                    vod_play_url: vod_play_url,
                    vod_play_from: first.title || site.name,
                    vod_remarks: tracks.length ? tracks.length + ' 集' : '',
                };
                cacheManager.set('detail', cacheKey, detail, 3600);
                return res.json(detail);
            }
            return res.status(404).json({ error: 'Not found' });
        }

        // 构建请求 URL
        const detailUrl = `${site.api}?ac=detail&ids=${encodeURIComponent(id)}`;
        const { data } = await fetchWithProxyFallback(detailUrl, { timeout: 8000 }, siteKey);

        if (data.list && data.list.length > 0) {
            const detail = data.list[0];
            cacheManager.set('detail', cacheKey, detail, 3600); // 缓存1小时
            res.json(detail);
        } else {
            res.status(404).json({ error: 'Not found' });
        }
    } catch (error) {
        console.error(`[Detail Error] ${site.name}:`, error.message);
        res.status(500).json({ error: 'Detail fetch failed' });
    }
});

// 4. 图片代理与缓存 API (Server-Side Image Caching)
app.get('/api/tmdb-image/:size/:filename', async (req, res) => {
    const { size, filename } = req.params;
    const allowSizes = ['w300', 'w342', 'w500', 'w780', 'w1280', 'original'];

    // 安全检查：size 走白名单；filename 只允许 TMDB 实际格式 <字母数字>.<jpg/png/webp>，
    // 收紧后不再放过 '..' 或多段点，杜绝任何路径穿越尝试
    if (!allowSizes.includes(size) || !/^[A-Za-z0-9]+\.(jpg|jpeg|png|webp)$/i.test(filename)) {
        return res.status(400).send('Invalid parameters');
    }

    const tmdbUrl = `https://image.tmdb.org/t/p/${size}/${filename}`;

    // Vercel环境或Serverless环境：不可写文件系统，直接转发流
    if (process.env.VERCEL) {
        try {
            // 支持自定义反代 URL
            let targetUrl = tmdbUrl;
            if (process.env['TMDB_PROXY_URL']) {
                const proxyBase = process.env['TMDB_PROXY_URL'].replace(/\/$/, '');
                targetUrl = `${proxyBase}/t/p/${size}/${filename}`;
            }

            console.log(`[Vercel Image] Proxying: ${targetUrl}`);
            const response = await axios({
                url: targetUrl,
                method: 'GET',
                responseType: 'stream',
                timeout: 10000
            });
            // 缓存控制：公共缓存，有效期1天
            res.setHeader('Cache-Control', 'public, max-age=86400, s-maxage=86400');
            response.data.pipe(res);
        } catch (error) {
            console.error(`[Vercel Image Error] ${tmdbUrl}:`, error.message);
            res.status(404).send('Image not found');
        }
        return;
    }

    // --- 本地/VPS 环境下启用磁盘缓存 ---
    const localPath = path.join(IMAGE_CACHE_DIR, size, filename);
    const localDir = path.dirname(localPath);

    // 1. 如果本地存在且文件大小 > 0，更新访问时间并返回
    if (fs.existsSync(localPath) && fs.statSync(localPath).size > 0) {
        // 更新文件的访问时间 (atime) 和修改时间 (mtime)，用于 LRU 清理
        try {
            const now = new Date();
            fs.utimesSync(localPath, now, now);
        } catch (e) { } // 忽略权限错误
        return res.sendFile(localPath);
    }

    // 2. 下载并缓存（支持 TMDB_PROXY_URL 代理）
    let fetchUrl = tmdbUrl;
    if (process.env['TMDB_PROXY_URL']) {
        const proxyBase = process.env['TMDB_PROXY_URL'].replace(/\/$/, '');
        fetchUrl = `${proxyBase}/t/p/${size}/${filename}`;
    }

    if (!fs.existsSync(localDir)) {
        try {
            fs.mkdirSync(localDir, { recursive: true });
        } catch (e) {
            console.error('[Cache Mkdir Error]', e.message);
            // 如果创建目录失败，降级为直接流式转发
            try {
                const response = await axios({ url: fetchUrl, method: 'GET', responseType: 'stream' });
                return response.data.pipe(res);
            } catch (err) { return res.status(404).send('Image not found'); }
        }
    }

    try {
        console.log(`[Image Proxy] Fetching: ${fetchUrl}`);
        const response = await axios({
            url: fetchUrl,
            method: 'GET',
            responseType: 'stream',
            timeout: 10000
        });

        const writer = fs.createWriteStream(localPath);

        // 使用 pipeline 处理流
        await pipeline(response.data, writer);

        // 下载完成后，检查缓存总大小并清理
        cleanCacheIfNeeded();

        // 发送文件
        res.sendFile(localPath);
    } catch (error) {
        console.error(`[Image Proxy Error] ${fetchUrl}:`, error.message);
        if (fs.existsSync(localPath)) {
            try { fs.unlinkSync(localPath); } catch (e) { }
        }
        res.status(404).send('Image not found');
    }
});

// ========== 缓存清理逻辑 ==========
const MAX_CACHE_SIZE_MB = 1024; // 1GB 缓存上限
const CLEAN_TRIGGER_THRESHOLD = 50; // 每添加50张新图检查一次 (减少IO压力)
let newItemCount = 0;

function cleanCacheIfNeeded() {
    newItemCount++;
    if (newItemCount < CLEAN_TRIGGER_THRESHOLD) return;
    newItemCount = 0;

    // 异步执行清理，不阻塞主线程
    setTimeout(() => {
        try {
            let totalSize = 0;
            let files = [];

            // 递归遍历缓存目录
            function traverseDir(dir) {
                if (!fs.existsSync(dir)) return;
                const items = fs.readdirSync(dir);
                items.forEach(item => {
                    const fullPath = path.join(dir, item);
                    const stats = fs.statSync(fullPath);
                    if (stats.isDirectory()) {
                        traverseDir(fullPath);
                    } else {
                        totalSize += stats.size;
                        files.push({ path: fullPath, size: stats.size, time: stats.mtime.getTime() });
                    }
                });
            }

            traverseDir(IMAGE_CACHE_DIR);

            const maxBytes = MAX_CACHE_SIZE_MB * 1024 * 1024;
            console.log(`[Cache Trim] Current size: ${(totalSize / 1024 / 1024).toFixed(2)} MB`);

            if (totalSize > maxBytes) {
                // 按时间排序，最旧的在前
                files.sort((a, b) => a.time - b.time);

                let deletedSize = 0;
                let targetDelete = totalSize - (maxBytes * 0.9); // 清理到 90%

                for (const file of files) {
                    if (deletedSize >= targetDelete) break;
                    try {
                        fs.unlinkSync(file.path);
                        deletedSize += file.size;
                    } catch (e) { console.error('Delete failed:', e); }
                }
                console.log(`[Cache Trim] Cleaned ${(deletedSize / 1024 / 1024).toFixed(2)} MB`);
            }
        } catch (err) {
            console.error('[Cache Trim Error]', err);
        }
    }, 100);
}

// 📱 扫码登录(见 lib/qr-login):电视出二维码,已登录的手机扫码确认后把本机登录凭据交给电视(取走即删,5 分钟过期)。
//    只在配了访问密码(有登录墙)时开。交过来的凭据只收配置里的访问密码(且没被封禁),其余不收
function qrLoginAuth(a) {
    if (!a || typeof a !== 'object' || a.type !== 'password') return null;
    const h = typeof a.hash === 'string' ? a.hash : '';
    const info = /^[a-f0-9]{64}$/.test(h) ? PASSWORD_HASH_MAP[h] : undefined;
    if (!info || !(info.index >= 0) || isBanned(h)) return null;
    return { type: 'password', hash: h };
}
let qrLogin = null;
try {
    qrLogin = require('./lib/qr-login').createQrLogin({
        enabled: () => ACCESS_PASSWORDS.length > 0,
        checkAuth: qrLoginAuth,
        limiter: (max) => rateLimit({ windowMs: 60 * 1000, max, keyGenerator: ipKey, message: { ok: false, message: '请求过于频繁，请稍后再试' } })
    });
    qrLogin.registerRoutes(app);
} catch (e) { console.warn('[QrLogin] 模块加载失败,扫码登录已禁用:', e.message); qrLogin = null; }

// 5. 认证检查 API
app.get('/api/auth/check', (req, res) => {
    // 检查是否需要密码
    res.json({
        requirePassword: ACCESS_PASSWORDS.length > 0,
        multiUserMode: ACCESS_PASSWORDS.length > 1,
        shareTrial: SHARE_TRIAL_SEC,
        qrLogin: !!qrLogin && ACCESS_PASSWORDS.length > 0
    });
});

// 6. 验证密码 API（支持多密码）
app.post('/api/auth/verify', (req, res) => {
    const { password, passwordHash } = req.body;

    // 无密码保护时直接通过
    if (ACCESS_PASSWORDS.length === 0) {
        return res.json({ success: true, syncEnabled: false });
    }

    // 计算输入的哈希值
    let inputHash;
    if (passwordHash) {
        inputHash = passwordHash;
    } else if (password) {
        inputHash = crypto.createHash('sha256').update(password).digest('hex');
    } else {
        return res.json({ success: false });
    }

    // 检查是否匹配任一密码
    const userInfo = PASSWORD_HASH_MAP[inputHash];
    if (userInfo !== undefined) {
        // 📊 独立密码登录也记进用户统计:真登录(password)记 last_login;会话恢复(passwordHash)只算一次活跃(模块内 5 分钟节流)。
        //    touchVisit 顺带记最近设备;它自己校验 token 是否真是已配置的密码,统计失败绝不影响登录。
        try {
            if (password && !passwordHash) touchUser(inputHash, { login: true });
            if (userStats) userStats.touchVisit(inputHash, req);
        } catch (e) { }
        // 密码有效
        res.json({
            success: true,
            passwordHash: inputHash,
            // 同步功能状态
            syncEnabled: userInfo.syncEnabled,
            userIndex: userInfo.index
        });
    } else {
        res.json({ success: false });
    }
});

// ==================== SEO 优化：影片详情页 ====================

/**
 * 生成 SEO 友好的影片/剧集详情页
 * 路由格式：/movie/:id 或 /tv/:id
 * 包含完整的 meta 标签和 JSON-LD 结构化数据
 */
app.get('/movie/:id', async (req, res) => {
    await renderMediaPage(req, res, 'movie');
});

app.get('/tv/:id', async (req, res) => {
    await renderMediaPage(req, res, 'tv');
});

async function renderMediaPage(req, res, mediaType) {
    const id = req.params.id;
    const TMDB_API_KEY = process.env.TMDB_API_KEY;

    // 🔒 TMDB ID 必须是纯数字，拒绝任何含特殊字符的 id（防注入到 TMDB URL 与 HTML）
    if (!/^\d+$/.test(id)) {
        return res.redirect('/');
    }

    if (!TMDB_API_KEY) {
        return res.redirect('/');
    }

    try {
        // 服务器端调用：根据 SERVER_IN_CHINA 环境变量决定是否使用代理
        const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];
        const serverInChina = process.env['SERVER_IN_CHINA'] === 'true';

        const baseUrl = (TMDB_PROXY_URL && serverInChina)
            ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3`  // 国内服务器使用代理
            : 'https://api.themoviedb.org/3';  // 海外服务器直连

        const detailUrl = `${baseUrl}/${mediaType}/${id}?api_key=${TMDB_API_KEY}&language=zh-CN`;

        const response = await axios.get(detailUrl, { timeout: 10000 });
        const data = response.data;

        const title = data.title || data.name || '未知影片';
        const overview = data.overview || '暂无简介';
        const posterPath = data.poster_path ? `https://image.tmdb.org/t/p/w500${data.poster_path}` : '';
        const backdropPath = data.backdrop_path ? `https://image.tmdb.org/t/p/original${data.backdrop_path}` : '';
        const releaseDate = data.release_date || data.first_air_date || '';
        const year = releaseDate ? releaseDate.split('-')[0] : '';
        const rating = data.vote_average ? data.vote_average.toFixed(1) : 'N/A';
        const genres = (data.genres || []).map(g => g.name).join(', ');
        const runtime = data.runtime || (data.episode_run_time && data.episode_run_time[0]) || 0;
        const siteUrl = getSiteUrl(req);

        // JSON-LD 结构化数据（让 Google 理解这是电影/电视剧）
        const jsonLd = {
            "@context": "https://schema.org",
            "@type": mediaType === 'movie' ? "Movie" : "TVSeries",
            "name": title,
            "description": overview,
            "image": posterPath,
            "datePublished": releaseDate,
            "aggregateRating": data.vote_average ? {
                "@type": "AggregateRating",
                "ratingValue": rating,
                "bestRating": "10",
                "ratingCount": data.vote_count || 0
            } : undefined,
            "genre": genres
        };

        // 🔒 预先 HTML 转义所有要插入页面的不可信文本（TMDB 数据可被社区编辑）
        const eTitle = escapeHtml(title);
        const eOverview = escapeHtml(overview);
        const eOverview160 = escapeHtml(overview.substring(0, 160));
        const eOverview200 = escapeHtml(overview.substring(0, 200));
        const eGenres = escapeHtml(genres);
        const eYear = escapeHtml(year);
        const eRating = escapeHtml(rating);
        const eRuntime = escapeHtml(runtime);
        const ePoster = escapeHtml(posterPath);
        const eBackdrop = escapeHtml(backdropPath || posterPath);
        // JSON-LD 注入 <script> 时必须转义 '<'，否则简介里的 </script> 可闭合标签造成 XSS
        const jsonLdSafe = JSON.stringify(jsonLd).replace(/</g, '\\u003c');

        // 生成完整的 HTML 页面
        const html = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>${eTitle} (${eYear}) - 在线观看 | E视界</title>
    <meta name="description" content="${eOverview160}">
    <meta name="keywords" content="${eTitle},${eYear},在线观看,免费电影,高清${mediaType === 'movie' ? '电影' : '电视剧'}">
    <meta name="robots" content="index, follow">
    <link rel="canonical" href="${siteUrl}/${mediaType}/${id}">
    
    <!-- Open Graph -->
    <meta property="og:type" content="${mediaType === 'movie' ? 'video.movie' : 'video.tv_show'}">
    <meta property="og:url" content="${siteUrl}/${mediaType}/${id}">
    <meta property="og:title" content="${eTitle} (${eYear}) - 在线观看">
    <meta property="og:description" content="${eOverview200}">
    <meta property="og:image" content="${ePoster}">
    <meta property="og:locale" content="zh_CN">

    <!-- Twitter Card -->
    <meta name="twitter:card" content="summary_large_image">
    <meta name="twitter:title" content="${eTitle} (${eYear})">
    <meta name="twitter:description" content="${eOverview200}">
    <meta name="twitter:image" content="${eBackdrop}">

    <!-- JSON-LD 结构化数据 -->
    <script type="application/ld+json">${jsonLdSafe}</script>
    
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; background: #141414; color: #fff; min-height: 100vh; }
        .hero { position: relative; height: 60vh; background-size: cover; background-position: center; }
        .hero::after { content: ''; position: absolute; inset: 0; background: linear-gradient(to top, #141414 0%, transparent 50%, rgba(0,0,0,0.5) 100%); }
        .content { position: relative; z-index: 1; max-width: 1200px; margin: 0 auto; padding: 20px; margin-top: -200px; display: flex; gap: 40px; }
        .poster { width: 300px; flex-shrink: 0; border-radius: 10px; box-shadow: 0 10px 30px rgba(0,0,0,0.5); }
        .info { flex: 1; }
        h1 { font-size: 2.5rem; margin-bottom: 10px; }
        .meta { color: #aaa; margin-bottom: 20px; }
        .meta span { margin-right: 20px; }
        .rating { color: #ffd700; }
        .overview { line-height: 1.8; color: #ccc; margin-bottom: 30px; }
        .btn-play { background: #e50914; color: #fff; border: none; padding: 15px 40px; font-size: 1.2rem; border-radius: 5px; cursor: pointer; text-decoration: none; display: inline-block; }
        .btn-play:hover { background: #f40612; }
        @media (max-width: 768px) { .content { flex-direction: column; margin-top: -100px; } .poster { width: 200px; margin: 0 auto; } h1 { font-size: 1.5rem; text-align: center; } }
    </style>
</head>
<body>
    <div class="hero" style="background-image: url('${eBackdrop}')"></div>
    <div class="content">
        ${posterPath ? `<img src="${ePoster}" alt="${eTitle}" class="poster">` : ''}
        <div class="info">
            <h1>${eTitle}</h1>
            <div class="meta">
                <span>${eYear}</span>
                ${runtime ? `<span>${eRuntime} 分钟</span>` : ''}
                <span class="rating">★ ${eRating}</span>
                ${genres ? `<span>${eGenres}</span>` : ''}
            </div>
            <p class="overview">${eOverview}</p>
            <a href="/?search=${encodeURIComponent(title)}" class="btn-play">▶ 立即观看</a>
        </div>
    </div>
    
    <!-- 自动跳转到主站搜索 (3秒后) -->
    <script>
        // 用户点击播放按钮或等待3秒后跳转到主站
        setTimeout(function() {
            // 不自动跳转，让用户主动点击
        }, 3000);
    </script>
</body>
</html>`;

        res.setHeader('Content-Type', 'text/html; charset=utf-8');
        res.setHeader('Cache-Control', 'public, max-age=86400'); // 缓存1天
        res.send(html);

    } catch (error) {
        console.error(`[SEO Page Error] ${mediaType}/${id}:`, error.message);
        res.redirect('/');
    }
}

/**
 * 动态生成 sitemap.xml
 * 包含热门电影和电视剧的 URL
 */
app.get('/sitemap.xml', async (req, res) => {
    const TMDB_API_KEY = process.env.TMDB_API_KEY;
    const siteUrl = getSiteUrl(req);
    const today = new Date().toISOString().split('T')[0];

    let urls = [
        // 首页
        `<url><loc>${siteUrl}/</loc><lastmod>${today}</lastmod><changefreq>daily</changefreq><priority>1.0</priority></url>`
    ];

    if (TMDB_API_KEY) {
        try {
            // 服务器端调用：根据 SERVER_IN_CHINA 环境变量决定是否使用代理
            // 如果服务器在国内，设置 SERVER_IN_CHINA=true
            const TMDB_PROXY_URL = process.env['TMDB_PROXY_URL'];
            const serverInChina = process.env['SERVER_IN_CHINA'] === 'true';

            const baseUrl = (TMDB_PROXY_URL && serverInChina)
                ? `${TMDB_PROXY_URL.replace(/\/$/, '')}/api/3`  // 国内服务器使用代理
                : 'https://api.themoviedb.org/3';  // 海外服务器直连

            // 获取热门电影 (前 40 部)
            const movieUrl = `${baseUrl}/movie/popular?api_key=${TMDB_API_KEY}&language=zh-CN&page=1`;
            const movieUrl2 = `${baseUrl}/movie/popular?api_key=${TMDB_API_KEY}&language=zh-CN&page=2`;

            const [movieRes1, movieRes2] = await Promise.all([
                axios.get(movieUrl, { timeout: 10000 }).catch(() => ({ data: { results: [] } })),
                axios.get(movieUrl2, { timeout: 10000 }).catch(() => ({ data: { results: [] } }))
            ]);

            const movies = [...(movieRes1.data.results || []), ...(movieRes2.data.results || [])];
            movies.forEach(m => {
                urls.push(`<url><loc>${siteUrl}/movie/${m.id}</loc><lastmod>${today}</lastmod><changefreq>weekly</changefreq><priority>0.8</priority></url>`);
            });

            // 获取热门电视剧 (前 40 部)
            const tvUrl = `${baseUrl}/tv/popular?api_key=${TMDB_API_KEY}&language=zh-CN&page=1`;
            const tvUrl2 = `${baseUrl}/tv/popular?api_key=${TMDB_API_KEY}&language=zh-CN&page=2`;

            const [tvRes1, tvRes2] = await Promise.all([
                axios.get(tvUrl, { timeout: 10000 }).catch(() => ({ data: { results: [] } })),
                axios.get(tvUrl2, { timeout: 10000 }).catch(() => ({ data: { results: [] } }))
            ]);

            const tvShows = [...(tvRes1.data.results || []), ...(tvRes2.data.results || [])];
            tvShows.forEach(t => {
                urls.push(`<url><loc>${siteUrl}/tv/${t.id}</loc><lastmod>${today}</lastmod><changefreq>weekly</changefreq><priority>0.8</priority></url>`);
            });

            console.log(`[Sitemap] Generated with ${movies.length} movies and ${tvShows.length} TV shows`);

        } catch (error) {
            console.error('[Sitemap Error]', error.message);
        }
    }

    const sitemap = `<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
${urls.join('\n')}
</urlset>`;

    res.setHeader('Content-Type', 'application/xml');
    res.setHeader('Cache-Control', 'public, max-age=3600'); // 缓存1小时
    res.send(sitemap);
});

// Helper: Get DB data (Local + Remote merged, Local XPTV sites take top priority)
function getDB() {
    let localDb = { sites: [] };
    try {
        if (fs.existsSync(DATA_FILE)) {
            localDb = JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'));
        }
    } catch (e) {
        console.error('[DB] Error reading local db.json:', e.message);
    }

    if (!remoteDbCache || !Array.isArray(remoteDbCache.sites)) {
        return localDb;
    }

    // 本地站点（尤其是 type:3 的 XPTV 扩展源和本地配置）作为主力最高优先级
    const mergedSites = [...(localDb.sites || [])];
    const seenKeys = new Set(mergedSites.map(s => s.key));

    for (const remoteSite of remoteDbCache.sites) {
        if (!seenKeys.has(remoteSite.key)) {
            seenKeys.add(remoteSite.key);
            mergedSites.push(remoteSite);
        }
    }

    return {
        ...remoteDbCache,
        ...localDb,
        sites: mergedSites
    };
}

// 本地/Docker 环境：启动服务器监听
// Vercel 环境下不需要调用 listen()，它会自动处理
if (!process.env.VERCEL) {
    app.listen(PORT, () => {
        console.log(`Server running on http://localhost:${PORT}`);
        console.log(`Image Cache Directory: ${IMAGE_CACHE_DIR}`);
        // P0-3 启动预热：立即后台预热首页各源 + 构建聚合缓存（不阻塞 listen 回调本身）
        // 预热并行填充 ext_cards 5 分钟缓存，首个 /api/home 请求即可秒回（各源走缓存命中）
        startupWarmup().catch(() => { });
    });
}

// 始终导出 app 模块 (Vercel Serverless 需要)
module.exports = app;
