// ==UserScript==
// @name         PokeLit Bot Lite (tự cập nhật)
// @namespace    local.pokelit.bot.lite.autoupdate
// @version      1.0.0
// @description  Bộ nạp: mỗi lần F5 tự dùng bản bot mới nhất từ kho GitHub (có bản lưu dự phòng khi mất mạng).
// @match        https://pokelit.0d4y.cc/*
// @run-at       document-start
// @noframes
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      raw.githubusercontent.com
// ==/UserScript==

(() => {
  'use strict';
  const FILE = 'pokelit-bot-lite.user.js';
  const BASE = 'https://raw.githubusercontent.com/tobinguyen999/mod/main/bots/';
  const KEY = 'bot_code:' + FILE, GUARD = 'plh_autoupdate_reload';
  const valid = t => typeof t === 'string' && t.length > 20000 && t.startsWith('// ==UserScript==') && t.includes("'use strict'");
  // Chạy bot trong trang (như @grant none): chèn thẻ <script> để bot thấy đúng window của game.
  const run = code => {
    const s = document.createElement('script');
    s.textContent = code + '\n//# sourceURL=bot-' + FILE;
    const put = () => { const root = document.head || document.documentElement; if (!root) return false; root.appendChild(s); s.remove(); return true; };
    if (!put()) { const mo = new MutationObserver(() => { if (put()) mo.disconnect(); }); mo.observe(document, { childList: true }); }
  };
  let cached = '';
  try { cached = GM_getValue(KEY, ''); } catch (_) {}
  if (valid(cached)) run(cached);   // chạy ngay bản đã lưu, không chờ mạng
  const t0 = performance.now();
  GM_xmlhttpRequest({
    method: 'GET', url: BASE + FILE + '?t=' + Date.now(), timeout: 15000, headers: { 'Cache-Control': 'no-cache' },
    onload: r => {
      try {
        const txt = r.responseText;
        if (r.status !== 200 || !valid(txt) || txt === cached) return;
        GM_setValue(KEY, txt);
        // Chỉ nạp lại ngay nếu tải xong trong vài giây đầu (chưa vào ván); nếu chậm thì bản mới dùng ở lần F5 sau để không mất ván đang chơi.
        let recent = false; try { recent = Date.now() - Number(sessionStorage.getItem(GUARD) || 0) < 30000; } catch (_) {}
        if (performance.now() - t0 < 5000 && !recent) { try { sessionStorage.setItem(GUARD, String(Date.now())); } catch (_) {} location.reload(); }
      } catch (_) {}
    },
    onerror: () => {}, ontimeout: () => {}
  });
})();
