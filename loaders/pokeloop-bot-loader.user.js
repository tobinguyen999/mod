// ==UserScript==
// @name         PokeLoop Bot Full (tự cập nhật)
// @namespace    local.pokeloop.bot.full.autoupdate
// @version      1.0.2
// @description  Bộ nạp: mỗi lần F5 tự dùng bản bot mới nhất từ kho GitHub (có bản lưu dự phòng khi mất mạng).
// @match        https://pokeloop.online/*
// @run-at       document-start
// @noframes
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      raw.githubusercontent.com
// ==/UserScript==

(() => {
  'use strict';
  const FILE = 'pokeloop-bot.user.js';
  const BASE = 'https://raw.githubusercontent.com/tobinguyen999/mod/main/bots/';
  const KEY = 'bot_code:' + FILE, GUARD = 'plh_autoupdate_reload';
  const valid = t => typeof t === 'string' && t.length > 20000 && t.startsWith('// ==UserScript==') && t.includes("'use strict'");
  const note = (msg, ms) => {   // thông báo nhỏ góc trái dưới để biết bộ nạp đang làm gì / lỗi gì
    try {
      const d = document.createElement('div');
      d.textContent = 'Bộ nạp bot: ' + msg;
      d.style.cssText = 'position:fixed;z-index:2147483647;left:8px;bottom:8px;max-width:70vw;background:#171923;color:#fff;padding:6px 10px;border:1px solid #65708a;border-radius:6px;font:12px sans-serif';
      const add = () => { (document.body || document.documentElement).appendChild(d); setTimeout(() => d.remove(), ms || 12000); };
      if (document.body || document.documentElement) add(); else addEventListener('DOMContentLoaded', add, { once: true });
    } catch (_) {}
  };
  // Chạy bot trong trang (như @grant none). Ưu tiên thẻ <script> nội tuyến (chạy đồng bộ, kịp trước game);
  // nếu CSP của trang chặn thì tự chuyển sang nạp bằng blob.
  const runBlob = code => {
    const url = URL.createObjectURL(new Blob([code + '\n//# sourceURL=bot-' + FILE], { type: 'text/javascript' }));
    const s = document.createElement('script');
    s.src = url;
    s.onerror = () => note('trang chặn không cho chạy bot (CSP). Báo lại cho Claude.', 20000);
    const root = document.head || document.documentElement; if (root) root.appendChild(s);
  };
  const run = code => {
    let blocked = false;
    const onViol = e => { if (/script/.test(e.effectiveDirective || '') && (e.blockedURI === 'inline' || !e.blockedURI)) { blocked = true; removeEventListener('securitypolicyviolation', onViol, true); runBlob(code); } };
    addEventListener('securitypolicyviolation', onViol, true);
    const s = document.createElement('script');
    s.textContent = code + '\n//# sourceURL=bot-' + FILE;
    const put = () => { const root = document.head || document.documentElement; if (!root) return false; root.appendChild(s); s.remove(); return true; };
    if (!put()) { const mo = new MutationObserver(() => { if (put()) mo.disconnect(); }); mo.observe(document, { childList: true }); }
    setTimeout(() => removeEventListener('securitypolicyviolation', onViol, true), 3000);
  };
  let cached = '';
  try { cached = GM_getValue(KEY, ''); } catch (_) {}
  if (valid(cached)) run(cached);   // chạy ngay bản đã lưu, không chờ mạng
  try { console.log('[Bộ nạp bot 1.0.2] đã chạy; bản lưu:', valid(cached) ? Math.round(cached.length / 1024) + ' KB' : 'chưa có'); } catch (_) {}
  note('đã chạy (1.0.2) · bản lưu: ' + (valid(cached) ? 'có' : 'chưa có, đang tải từ GitHub…'), 6000);
  const t0 = performance.now();
  GM_xmlhttpRequest({
    method: 'GET', url: BASE + FILE + '?t=' + Date.now(), timeout: 15000, headers: { 'Cache-Control': 'no-cache' },
    onload: r => {
      try {
        const txt = r.responseText;
        if (r.status !== 200 || !valid(txt)) { if (!valid(cached)) note('GitHub trả mã ' + r.status + ' hoặc file lỗi.', 20000); return; }
        if (txt === cached) return;
        GM_setValue(KEY, txt);
        try { console.log('[Bộ nạp bot] đã tải bản mới', Math.round(txt.length / 1024) + ' KB'); } catch (_) {}
        // Chỉ nạp lại ngay nếu tải xong trong vài giây đầu (chưa vào ván); nếu chậm thì bản mới dùng ở lần F5 sau để không mất ván đang chơi.
        let recent = false; try { recent = Date.now() - Number(sessionStorage.getItem(GUARD) || 0) < 30000; } catch (_) {}
        if (performance.now() - t0 < 5000 && !recent) { try { sessionStorage.setItem(GUARD, String(Date.now())); } catch (_) {} location.reload(); }
      } catch (_) {}
    },
    onerror: e => { if (!valid(cached)) note('không tải được bot từ GitHub (kiểm tra quyền raw.githubusercontent.com trong Tampermonkey).', 20000); },
    ontimeout: () => { if (!valid(cached)) note('tải bot từ GitHub quá lâu, thử F5 lại.', 20000); }
  });
})();
