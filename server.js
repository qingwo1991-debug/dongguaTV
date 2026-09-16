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
const PASSWORD_HASH_MAP = {};
ACCESS_PASSWORDS.forEach((pwd, index) => {
    const hash = crypto.createHash('sha256').update(pwd).digest('hex');
    PASSWORD_HASH_MAP[hash] = {
        index: index,
        // 第一个密码不启用同步（保持现有设计），其他密码启用同步
        syncEnabled: index > 0
    };
});

console.log(`[System] Password mode: ${ACCESS_PASSWORDS.length > 1 ? 'Multi-user' : 'Single'} (${ACCESS_PASSWORDS.length} passwords)`);

// 远程配置URL
const REMOTE_DB_URL = process.env['REMOTE_DB_URL'] || '';
// 远程配置 URL 的代理（r2.dev 等需代理访问的地址；未设置则不代理）
const REMOTE_DB_PROXY = process.env['REMOTE_DB_PROXY'] || '';

// CORS 代理 URL（用于中转无法直接访问的资源站 API）
const CORS_PROXY_URL = process.env['CORS_PROXY_URL'] || '';

// 环境变量加载状态日志（用于 Vercel 调试）
console.log(`[System] Environment: ${process.env.VERCEL ? 'Vercel Serverless' : 'Local/VPS'}`);
console.log(`[System] TMDB_API_KEY: ${process.env.TMDB_API_KEY ? '✓ Configured' : '✗ Missing'}`);
console.log(`[System] TMDB_PROXY_URL: ${process.env['TMDB_PROXY_URL'] || '(not set)'}`);
console.log(`[System] CORS_PROXY_URL: ${CORS_PROXY_URL || '(not set)'}`);
console.log(`[System] REMOTE_DB_URL: ${REMOTE_DB_URL ? '✓ Configured' : '(not set)'}`);



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

// 缓存配置
const CACHE_TYPE = process.env.CACHE_TYPE || 'json'; // json, sqlite, memory, none
const SEARCH_CACHE_JSON = path.join(__dirname, 'cache_search.json');
const DETAIL_CACHE_JSON = path.join(__dirname, 'cache_detail.json');
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
        this.db = null;
        this.init();
    }

    init() {
        if (this.type === 'json') {
            if (fs.existsSync(SEARCH_CACHE_JSON)) {
                try { this.searchCache = JSON.parse(fs.readFileSync(SEARCH_CACHE_JSON)); } catch (e) { }
            }
            if (fs.existsSync(DETAIL_CACHE_JSON)) {
                try { this.detailCache = JSON.parse(fs.readFileSync(DETAIL_CACHE_JSON)); } catch (e) { }
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

    get(category, key) {
        if (this.type === 'memory') {
            const data = category === 'search' ? this.searchCache[key] : this.detailCache[key];
            if (data && data.expire > Date.now()) return data.value;
            return null;
        } else if (this.type === 'json') {
            const data = category === 'search' ? this.searchCache[key] : this.detailCache[key];
            if (data && data.expire > Date.now()) return data.value;
            return null;
        } else if (this.type === 'sqlite' && this.db) {
            try {
                const row = this.db.prepare(
                    'SELECT value FROM cache WHERE category = ? AND key = ? AND expire > ?'
                ).get(category, key, Date.now());
                return row ? JSON.parse(row.value) : null;
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
            if (category === 'search') this.searchCache[key] = item;
            else this.detailCache[key] = item;
        } else if (this.type === 'json') {
            const item = { value, expire };
            if (category === 'search') this.searchCache[key] = item;
            else this.detailCache[key] = item;
            this.saveDisk();
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

    saveDisk() {
        if (this.type === 'json') {
            fs.writeFileSync(SEARCH_CACHE_JSON, JSON.stringify(this.searchCache));
            fs.writeFileSync(DETAIL_CACHE_JSON, JSON.stringify(this.detailCache));
        }
    }

    // 定期清理过期缓存 (SQLite)
    cleanup() {
        if (this.type === 'sqlite' && this.db) {
            try {
                const result = this.db.prepare('DELETE FROM cache WHERE expire < ?').run(Date.now());
                if (result.changes > 0) {
                    console.log(`[SQLite Cache] Cleaned ${result.changes} expired entries`);
                }
            } catch (e) {
                console.error('[SQLite Cache] Cleanup error:', e.message);
            }
        }
    }
}

const cacheManager = new CacheManager(CACHE_TYPE);

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

// ⚠️ 关键：动态注入站点 URL 到 index.html
// 自动将 meta 标签中的 ednovas.video 替换为当前访问的网站地址
app.get(['/', '/index.html'], (req, res) => {
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

app.get('/api/config', (req, res) => {
    // 检查请求中的 token 是否支持同步
    const userToken = req.query.token || '';
    const userInfo = PASSWORD_HASH_MAP[userToken];
    const syncEnabled = userInfo ? userInfo.syncEnabled : false;

    res.json({
        tmdb_api_key: process.env.TMDB_API_KEY,
        tmdb_proxy_url: process.env['TMDB_PROXY_URL'],
        // CORS 代理 URL（用于中转无法直接访问的资源站 API）
        cors_proxy_url: CORS_PROXY_URL || null,
        // Vercel 环境下禁用本地图片缓存，防止写入报错
        enable_local_image_cache: !IS_VERCEL,
        // 多用户同步功能
        sync_enabled: syncEnabled,
        multi_user_mode: ACCESS_PASSWORDS.length > 1
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
        const stmt = cacheManager.db.prepare('SELECT item_id, item_data, updated_at FROM user_history WHERE user_token = ?');
        const rows = stmt.all(userToken);

        const history = rows.map(row => ({
            id: row.item_id,
            data: JSON.parse(row.item_data),
            updated_at: row.updated_at
        }));

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
        let deleted = 0;
        const transaction = cacheManager.db.transaction((items) => {
            // 1. 插入/更新本地有的记录
            for (const item of items) {
                if (item.id && item.data) {
                    insertStmt.run(
                        token,
                        item.id,
                        JSON.stringify(item.data),
                        item.updated_at || Date.now()
                    );
                    saved++;
                }
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

// TMDB 通用代理与缓存 API
const TMDB_CACHE_TTL = 3600 * 10; // 缓存 10 小时
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
        cacheManager.set('detail', cacheKey, response.data, TMDB_CACHE_TTL);
        res.json(response.data);
    } catch (error) {
        console.error(`[TMDB Proxy Error] ${tmdbPath}:`, error.message);
        res.status(error.response?.status || 500).json({ error: 'Proxy request failed' });
    }
});

// M3U8 代理 - 用于广告过滤分析（绕过 CORS 限制）
app.get('/api/m3u8-proxy', async (req, res) => {
    const url = req.query.url;
    if (!url) {
        return res.status(400).json({ error: 'Missing url parameter' });
    }

    // 安全检查：只允许 .m3u8 URL
    try {
        const parsedUrl = new URL(url);
        if (!parsedUrl.pathname.endsWith('.m3u8') && !parsedUrl.pathname.includes('.m3u8')) {
            return res.status(400).json({ error: 'Only .m3u8 URLs are allowed' });
        }
        if (!['http:', 'https:'].includes(parsedUrl.protocol)) {
            return res.status(400).json({ error: 'Invalid protocol' });
        }
    } catch (e) {
        return res.status(400).json({ error: 'Invalid URL' });
    }

    try {
        const response = await axios.get(url, {
            timeout: 8000,
            responseType: 'text',
            headers: {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
        });
        res.set('Content-Type', 'text/plain; charset=utf-8');
        res.set('Cache-Control', 'no-cache');
        res.send(response.data);
    } catch (err) {
        console.error(`[M3U8 Proxy] Failed: ${url.substring(0, 80)}`, err.message);
        res.status(502).json({ error: 'Failed to fetch M3U8', details: err.message });
    }
});

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
    if (extManifestCache.size > 300) extManifestCache.delete(extManifestCache.keys().next().value);
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
        if (extPlayinfoCache.size > 500) {
            const firstKey = extPlayinfoCache.keys().next().value;
            extPlayinfoCache.delete(firstKey);
        }
    }
}

async function resolveExtMediaUrl(site, rawUrl, playArgs = {}) {
    const cached = getCachedExtPlayinfo(rawUrl);
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

    const cached = getCachedExtPlayinfo(rawUrl);
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
            const cachedM3u8 = getCachedExtPlayinfo(rawUrl);
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
        const cachedManifest = getCachedExtManifest(upstreamUrl);
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

        const results = rawItems.map(item => {
            const id = String(item.vod_id || item.id || item.ext?.id || '');
            const name = item.vod_name || item.name || item.title || '';
            const remarks = String(item.vod_remarks || item.remarks || item.subTitle || '').replace(/<[^>]+>/g, '').trim();
            const scoreMatch = remarks.match(/([\d\.]+)分/);
            const score = scoreMatch ? parseFloat(scoreMatch[1]) : 8.8;

            return {
                id: `ext_${siteKey}_${id}`,
                vod_id: id,
                title: name,
                name: name,
                original_title: '',
                original_name: '',
                poster_path: item.vod_pic || item.pic || item.cover || item.poster || '',
                detail_url: item.ext?.url || item.ext?.play_url || '',
                vote_average: score,
                release_date: remarks || '精选',
                first_air_date: remarks || '精选',
                remarks: remarks,
                site_key: siteKey,
                site_name: site.name
            };
        });

        const data = { results, total_pages: 5, page, route: routeUsed };
        if (results.length > 0) {
            cacheManager.set('detail', cacheKey, data, 300); // 推荐列表缓存 5 分钟，兼顾实时更新与加载速度
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
        console.error(`[Ext Cards Error] ${site.name}:`, err.message);
        res.status(500).json({ error: 'Failed to fetch cards', results: [] });
    }
});

// 1. 获取站点列表
app.get('/api/sites', async (req, res) => {
    // 尝试从远程加载以更新 remoteDbCache
    if (REMOTE_DB_URL) {
        const now = Date.now();
        if (!remoteDbCache || (now - remoteDbLastFetch >= REMOTE_DB_CACHE_TTL)) {
            try {
                const reqOpts = { timeout: 10000, proxy: false };
                const response = await axios.get(REMOTE_DB_URL, reqOpts);
                if (response.data && Array.isArray(response.data.sites)) {
                    remoteDbCache = response.data;
                    remoteDbLastFetch = now;
                    console.log('[Remote] Config loaded successfully');
                }
            } catch (err) {
                console.error('[Remote] Failed to load config:', err.message);
            }
        }
    }

    res.json(getDB());
});

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

    const sites = getDB().sites;
    const includeNsfw = truthyFlag(req.query.include_nsfw);

    if (!stream) {
        // 非流式模式：返回聚合的 JSON 结果（用于 refreshEpisodes 查找 vod_id）
        const siteKey = req.query.site_key;  // 可选：只搜索指定站点
        // 指定 site_key 时按原站点查（刷新集数/线路）；全站搜索才受成人过滤控制
        const targetSites = siteKey
            ? sites.filter(s => s.key === siteKey)
            : (includeNsfw ? sites : sites.filter(s => !isNsfwSite(s)));

        const allResults = [];
        const searchPromises = targetSites.map(async (site) => {
            const cacheKey = `${site.key}_${keyword}`;
            const cached = cacheManager.get('search', cacheKey);
            if (cached && cached.list) {
                cached.list.forEach(item => {
                    allResults.push({ ...item, site_key: site.key, site_name: site.name });
                });
                return;
            }
            try {
                if (isExtSite(site)) {
                    // XPTV js 扩展源: 调用 search()
                    const extList = await extSearch(site, keyword);
                    cacheManager.set('search', cacheKey, { list: extList }, 3600);
                    allResults.push(...(extList.map(item => ({ ...item, site_key: site.key, site_name: site.name }))));
                    return;
                }
                const searchUrl = `${site.api}?ac=detail&wd=${encodeURIComponent(keyword)}`;
                const { data } = await fetchWithProxyFallback(searchUrl, { timeout: 8000 }, site.key);
                const list = data.list ? data.list.map(item => ({
                    vod_id: item.vod_id,
                    vod_name: item.vod_name,
                    vod_pic: item.vod_pic,
                    vod_play_url: item.vod_play_url,
                    site_key: site.key,
                    site_name: site.name
                })) : [];
                cacheManager.set('search', cacheKey, { list }, 3600);
                allResults.push(...list);
            } catch (err) {
                console.error(`[Search JSON] ${site.name}:`, err.message);
            }
        });
        await Promise.all(searchPromises);
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
    const searchPromises = searchSites.map(async (site) => {
        // 对每个站点，尝试所有关键词变体
        const allResults = [];

        for (const kw of searchKeywords) {
            const cacheKey = `${site.key}_${kw}`;
            const cached = cacheManager.get('search', cacheKey);

            if (cached && cached.list) {
                // 命中缓存
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

                    // 缓存结果 (1小时)
                    cacheManager.set('search', cacheKey, { list }, 3600);

                    allResults.push(...list);
                } catch (error) {
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
                    site_name: site.name
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
    const sites = getDB().sites;
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });

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
            cacheManager.set('search', cacheKey, result, 3600);
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

        cacheManager.set('search', cacheKey, result, 3600); // 缓存1小时
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
    const sites = getDB().sites;
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });

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
    const sites = getDB().sites;
    const site = sites.find(s => s.key === siteKey);

    if (!site) return res.status(404).json({ error: 'Site not found' });

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

// 5. 认证检查 API
app.get('/api/auth/check', (req, res) => {
    // 检查是否需要密码
    res.json({
        requirePassword: ACCESS_PASSWORDS.length > 0,
        multiUserMode: ACCESS_PASSWORDS.length > 1
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
    });
}

// 始终导出 app 模块 (Vercel Serverless 需要)
module.exports = app;
