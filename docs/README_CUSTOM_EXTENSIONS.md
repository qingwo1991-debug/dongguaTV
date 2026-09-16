# 冬瓜 TV (Donggua-TV) 定制扩展与升级维护全指南 (XPTV 2.0 全面集成版)

本指南详细记录了在冬瓜 TV（`donggua-tv:3099`）上实现的**XPTV JS 扩展沙箱 2.0 执行器、YueChan XPTV.json 全部 20 个源 + 黄果短剧共 21 个独立首页专区、通用同源 HLS/MP4 播放代理、逐集真实媒体解析、AES 图片解密代理、全网搜索优先级、成人过滤联动、集数自然排序与秒开优化**等全部定制架构与代码，以便在后续 Docker 镜像升级或系统迁移时能够**秒级还原或一键合入**。

---

## 目录
1. [核心挂载与数据保护机制](#1-核心挂载与数据保护机制)
2. [定制功能与专区清单](#2-定制功能与专区清单)
3. [一键升级与补丁合入（推荐）](#3-一键升级与补丁合入推荐)
4. [核心文件结构与职责划分](#4-核心文件结构与职责划分)
5. [架构与代码实现规范](#5-架构与代码实现规范)
   - [5.1 XPTV 通用沙箱执行器 2.0 (executor.js)](#51-xptv-通用沙箱执行器-20-executorjs)
   - [5.2 后端服务改造 (server.js)](#52-后端服务改造-serverjs)
   - [5.3 前端页面与播放器改造 (index.html)](#53-前端页面与播放器改造-indexhtml)
   - [5.4 站点数据库配置 (db.json)](#54-站点数据库配置-dbjson)
   - [5.5 容器编排配置 (docker-compose.yml)](#55-容器编排配置-docker-composeyml)
6. [快速验证与健康检查指令](#6-快速验证与健康检查指令)

---

## 1. 核心挂载与数据保护机制

当前在 `/root/docker/docker-compose.yml` 中采用了 **宿主机文件与模块绑定挂载（Bind Mount）** 策略：

```yaml
    environment:
      - NODE_PATH=/app/custom_modules:/app/node_modules
    volumes:
      - ./dongguatv/db.json:/app/db.json
      - ./dongguatv/cache.db:/app/cache.db
      - ./dongguatv/cache/images:/app/public/cache/images
      - ./dongguatv/node_modules:/app/custom_modules
      - ./dongguatv/server.js:/app/server.js
      - ./dongguatv/executor.js:/app/executor.js
      - ./dongguatv/js_cache:/app/js_cache
      - ./dongguatv/index.html:/app/public/index.html
```

### 为什么日常重启/拉取不会“一切归零”？
- `server.js`、`index.html`、`executor.js`、`db.json`、`node_modules`（包含 `cheerio`、`crypto-js`、`iconv-lite`）保存在宿主机目录 `/root/docker/dongguatv/` 中。
- 当执行 `docker compose pull` 或 `docker compose up -d` 时，Docker 仅更新镜像底层，**容器启动时依然会自动挂载宿主机上的这套定制代码和扩展库**，零数据丢失。

---

## 2. 定制功能与专区清单

| 功能专区 / 模块 | 解决的痛点 | 实现机制 |
| :--- | :--- | :--- |
| **XPTV 沙箱引擎 2.0** | 支持运行任意复杂 XPTV / TvCat JS 脚本 (加密、网页解析、GBK转码) | Node.js `node:vm` 沙箱 + `CryptoJS` + `cheerio` + `iconv-lite` + `makeDualArg` 参数双模包装 |
| **黄果短剧专区** | 首页精选短剧直达与榜单浏览（受成人过滤保护） | `/api/ext/cards` 接口聚合 + 首页独立 Row / Category 导航 |
| **河马剧场专区** | 热门全网短剧（微短剧、重生、都市逆袭、甜宠等） | 接入 `csp_kuaikaw`，首页推荐 + 60+集极速直链秒播 |
| **AGE 动漫专区** | 经典与新番连载动漫追更 | 接入 `csp_age`，自动解析非凡/暴风/无尽多线 M3U8 |
| **皮皮影视专区** | 高清院线电影与热门电视剧 | 接入 `csp_ppnix`，自适应 IPFS/分片与动态 M3U8 代理 |
| **全量 XPTV 首页矩阵** | 远程配置中的源虽能搜索但首页不可见 | YueChan `XPTV.json` 全部 20 源均建立独立 Row 与分类入口；失效源在 15 秒后结束加载，不永久转圈 |
| **逐集媒体解析** | 河马/AGE 等第2集后仍是播放页 URL，MP4 被误当 HLS | `/api/ext/resolve-play` 按 `site_key` 调用正确扩展脚本，切集前解析真实 MP4/M3U8 类型 |
| **全网搜索高优先级** | 搜索剧名时优先展示高清无广告 XPTV 精品源 | 提升 XPTV 源至 `db.json` 首位 + SSE 流式即时推送 |
| **秒开快速机制** | 本地从点击卡片到播放的延迟痛点 | 首页前 10 部并行缓存结构、前 4 部预解析首集 + 后续 3 集预热；视频卡片悬停/触摸预取详情与 M3U8；热缓存详情约 **0.02s** |
| **媒体与脚本缓存** | 重复 VM 编译、重复解析页面 | `vm.Script` 预编译缓存 + 15 分钟媒体直链缓存 + in-flight 请求去重 + 2 分钟重写清单缓存 |
| **自动换网络路径** | 部分源直连/代理返回空页或 500 | 推荐列表空 × 自动多次尝试“代理 → 直连”两种路径；执行器支持 301→308 跳转跟随 + `rejectUnauthorized:false` 容忍过期证书 |
| **通用 HLS / MP4 代理** | 解决各站点防盗链、CORS 跨域、AES 解密与 strict MIME 限制 | `/api/ext-hls-proxy` 实时重写 M3U8 清单、中转 AES-128 密钥及分片，自动适配 Referer / Origin |
| **AES 封面解密代理** | 修复短剧加密封面无法直接加载展示的问题 | `/api/ext-image-proxy` AES-128-CBC 解密 + 本地磁盘缓存 |

---

## 3. 一键升级与补丁合入（推荐）

在 `/root/docker/dongguatv/` 目录下预置有一键维护脚本 `upgrade_and_patch.sh`：

```bash
cd /root/docker/dongguatv
./upgrade_and_patch.sh
```

### 脚本执行流程：
1. **自动备份**：将当前所有定制文件及补丁备份至 `backup_YYYYMMDD_HHMMSS/`。
2. **拉取新镜像**：提取新版镜像中的干净源码 `server.js` 和 `index.html`。
3. **自动打补丁**：将 `server.js.patch` 与 `index.html.patch` 自动合入新版本代码。
4. **依赖检查**：自动检测并安装缺失的 `cheerio` / `crypto-js` / `iconv-lite` 模块。
5. **重启容器**：执行 `docker compose up -d --force-recreate donggua-tv`。
6. **健康检查**：自动验证接口状态。

---

## 4. 核心文件结构与职责划分

```text
/root/docker/dongguatv/
├── executor.js                  # [核心独立模块] XPTV 2.0 沙箱引擎、双模参数适配与极速网络隧道
├── server.js                    # [后端核心] Express 服务端（扩展卡片聚合、并发加速、通用 HLS 代理）
├── index.html                   # [前端核心] Vue 3 单页应用（4大专区导航、卡片直开播放、成人过滤）
├── db.json                      # [站点数据] 站点配置列表（XPTV 扩展源置顶优先）
├── node_modules/                # [宿主机挂载] cheerio, crypto-js, iconv-lite 等 XPTV 依赖
├── server.js.patch              # [补丁文件] server.js 差异补丁
├── index.html.patch             # [补丁文件] index.html 差异补丁
├── upgrade_and_patch.sh         # [自动化工具] 一键升级与自动合入脚本
└── README_CUSTOM_EXTENSIONS.md  # [本说明文档]
```

---

## 5. 架构与代码实现规范

### 5.1 XPTV 通用沙箱执行器 2.0 (`executor.js`)
`executor.js` 是一个完全独立的模块，无需修改上游任何第三方依赖包：
- **完整 XPTV API 全局注入**：注入 `createCryptoJS()`、`createCheerio()`、`createIconv()`、`$cache`、`$print`、`$fetch`、`$get`、`$post`、`jsonify`、`argsify`、`fetchHtml`、`URL`、`URLSearchParams`、`atob`、`btoa`、`$html` 等。
- **参数双模适配 (`makeDualArg`)**：允许 JS 扩展内部既可以使用 `ext.id` 直接读取属性，又可以使用 `JSON.parse(ext)` 不报语法错误。
- **智能分流网络隧道**：先 2.5s 直连尝试；超时或连接重置时立即自动切换至 `mihomo:7890` TLS CONNECT 隧道，保障被墙或海外源高可用。

### 5.2 后端服务改造 (`server.js`)
1. **通用卡片接口 (`/api/ext/cards`)**：接收 `site_key`、`tab`、`page`，支持黄果短剧、河马微短剧、AGE动漫、皮皮影视等所有 XPTV 站点的首页与分类列表。
2. **详情并行加载与预解析 (`/api/detail`)**：
   - 优先命中 24h 剧集结构缓存。
   - 未命中时采用 `Promise.all` 并发拉取剧集列表与第 1 集真实播放地址。
   - 后台静默预解析第 2 集，消除选集与自动下一集的卡顿。
3. **通用同源 HLS 播放代理 (`/api/ext-hls-proxy/:resource`)**：
   - 动态识别并伪装目标源的 `Referer` 与 `Origin`。
   - 重写 M3U8 清单中的子清单、AES-128 Key 和 TS 分片。
   - 默认分片扩展名规范化为 `.ts`，彻底消除 ffmpeg / Safari / ExoPlayer 对非法扩展名的报错。

### 5.3 前端页面与播放器改造 (`index.html`)
1. **首页四大专区**：
   - `huangguoRow`: 黄果短剧·魔改精选（受成人过滤控制）
   - `kuaikawRow`: 河马剧场·微短剧（全龄开放）
   - `ageRow`: AGE动漫·番剧追更（全龄开放）
   - `ppnixRow`: 皮皮影视·超清影院（全龄开放）
2. **卡片智能路由 (`openCard`)**：
   识别扩展源卡片（携带 `site_key` 与 `vod_id`），点击直接调起详情并开始播放，绕过全网全量搜索耗时。
3. **全源扩展识别 (`isExtSiteKey`)**：
   对所有扩展站点自动跳过不必要的前端测速直接投送播放，并在播放时走同源 HLS 代理。

---

## 6. 快速验证与健康检查指令

在宿主机终端执行以下脚本，即可全自动检测整套服务是否正常：

```bash
# 1. 验证四大专区卡片接口
curl -s "http://127.0.0.1:3099/api/ext/cards?site_key=huangguo&tab=home&page=1" | jq .results[0].title
curl -s "http://127.0.0.1:3099/api/ext/cards?site_key=kuaikaw&tab=home&page=1" | jq .results[0].title
curl -s "http://127.0.0.1:3099/api/ext/cards?site_key=age&tab=home&page=1" | jq .results[0].title
curl -s "http://127.0.0.1:3099/api/ext/cards?site_key=ppnix&tab=home&page=1" | jq .results[0].title

# 2. 验证剧集解析与首集直链
curl -s "http://127.0.0.1:3099/api/detail?site_key=kuaikaw&id=41000337324" | jq .list[0].vod_remarks
curl -s "http://127.0.0.1:3099/api/detail?site_key=age&id=20260230" | jq .list[0].vod_remarks

# 3. 验证同源 HLS 代理与视频流硬解解码 (测试 2 秒)
ffmpeg -y -t 2 -i "http://127.0.0.1:3099/api/ext-hls-proxy/stream.m3u8?url=https%3A%2F%2Fwww.ppnix.com%2Finfo%2Fm3u8%2F8458%2F1080P.m3u8" -f null -
```
