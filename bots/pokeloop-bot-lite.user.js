// ==UserScript==
// @name         PokeLoop Bot Lite
// @namespace    local.pokeloop.bot.lite
// @version      0.9.20
// @description  Bản rút gọn cho PokéLoop (pokeloop.online): bot chơi + mở hòm + rift, không báo cáo. Khai đúng cờ 'auto' với game. Chỉ bật một bot tại một thời điểm.
// @match        https://pokeloop.online/*
// @run-at       document-start
// @updateURL    https://raw.githubusercontent.com/tobinguyen999/mod/main/bots/pokeloop-bot-lite.user.js
// @downloadURL  https://raw.githubusercontent.com/tobinguyen999/mod/main/bots/pokeloop-bot-lite.user.js
// @grant        none
// @inject-into  page
// ==/UserScript==

(() => {
  'use strict';
  const W = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;
  if (W.__PLH_ACTIVE) return;
  W.__PLH_ACTIVE = true;
  const bootDiag = { rewritten: false, regexMatched: false };

  const isIOS = /iPhone|iPad|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1) || W.matchMedia('(pointer:coarse)').matches;

  const VERSION = '0.9.20 Loop Lite';
  const TAG = '[PokeLoop Bot]';
  const DEFAULTS = {
    enabled: true,
    dodge: true,
    loot: true,
    chest: true,
    buff: true,
    events: true,
    bigEvent: true,
    vi: true,
    learnRec: true,
    learnUse: true,
    learnMix: 0.5,
    autoRift: true,
    coop: true,
    ticketFocus: true,
    titanMode: true,
    judgeMode: true,
    yieldInput: true,   // v0.9.16: phím/tay cầm thật của bạn ghi đè bot 0,9 giây (như auto của dev)
    shopBuy: false,
    shopWant: ['lifeorb', 'choiceband', 'leftovers'],
    itemPick: false,
    itemLock: true,
    itemWant: ['lifeorb', 'choiceband', 'leftovers'],
    cardPick: false,
    cardReroll: true,
    cardMon: '',
    cardStats: ['hp', 'atk', 'xp'],
    cardMoves: {},
    chestForce: false,
    relocate: true,
    autoPick: true,
    priorities: ['hp', 'regen', 'defense', 'damage', 'cooldown', 'area', 'speed', 'magnet', 'experience'],
    reroll: true,
    rerollThreshold: 150,
    autoRestart: false,
    restartDelay: 10,
    background: !isIOS,
    bgAudio: true,   // v0.9.14: phát âm thanh im lặng khi tab ẩn để trình duyệt ít giảm tốc
    autoDownload: true,
    chestHunt: true,
    chestExplore: true,
    chestRange: 4000,
    perfMode: true
  };

  const state = {
    ...DEFAULTS,
    ...(() => { try { return JSON.parse(localStorage.getItem('plh_settings') || '{}'); } catch (_) { return {}; } })()
  };
  // Lite: tắt học từ người chơi và toàn bộ báo cáo (vẫn giữ tự mua Kecleon)
  state.learnRec = false; state.learnUse = false; state.autoDownload = false;
  if (!Array.isArray(state.priorities)) state.priorities = [...DEFAULTS.priorities];
  if (!Array.isArray(state.shopWant)) state.shopWant = [...DEFAULTS.shopWant];
  if (!Array.isArray(state.itemWant)) state.itemWant = [...DEFAULTS.itemWant];
  if (!Array.isArray(state.cardStats)) state.cardStats = [...DEFAULTS.cardStats];
  if (!state.cardMoves || typeof state.cardMoves !== 'object' || Array.isArray(state.cardMoves)) state.cardMoves = {};
  if (typeof state.cardMon !== 'string') state.cardMon = '';
  state.autoPick = true; // v0.8.6: tự chọn thẻ luôn đi theo công tắc Bot (Bot bật = bot chọn thẻ, Bot tắt = bạn tự chọn)

  const reportPrefs = { autoDownload: state.autoDownload !== false };
  const panelPrefs = { min: isIOS, hidden: false };
  const logged = new Set();
  const loggedErrors = new Set();
  const wrapped = { axis: false, level: false, pick: false, offer: false };

  let pendingCardOffer = null;
  let botVector = [0, 0];
  let botMode = 'né';
  let panelDrag = null;
  let btnToggleDrag = null, btnMenuDrag = null;
  let enemyHistory = new Map();
  let relocate = { active: false, goal: null, until: 0, left: [], lowThreatSince: 0, disarmed: false, denseSince: 0 };
  let activeChaseId = null, chaseStart = 0, chaseBan = 0;
  let pathCache = { key: '', at: 0, point: null, reachable: false, route: [] };
  let goalState = { key: '', goal: null, mode: '', since: 0, lowThreatSince: 0, reason: 'khởi tạo' };

  let currentTarget = '';
  let waitState = { since: 0, cooldownUntil: 0 };
  let targetReason = '';
  let targetReasonChangedAt = Date.now();

  let stickyRift = null;
  let stickySpecial = null;
  let mapMem = new Map();
  let sectorThreat = new Array(8).fill(0), sectorLoot = new Array(8).fill(0), sectorShots = new Array(8).fill(0);
  let eventInfo = { name: '', list: [] };
  const chestTrack = new Map();
  let pinHist = [];
  let lootTrack = { key: '', t0: 0, d0: 0, nearSince: 0 };
  let lastProjectileLog = 0, lastProjectileCount = null;
  let restartRequested = false;
  let lastSpecialScan = 0, cachedSpecials = [], cachedNearestSpecial = null;

  // Giới hạn tần suất đổi mode (tối thiểu 1.2s)
  let lastModeChangeAt = 0;
  let lastBotMode = 'né';

  // State cho chế độ Tuần tra (Patrol Kiting)
  let patrolAngle = 0;
  let patrolStartPos = null;
  let patrolLastT = 0;
  function patrolStep(radPerSec) { const t = Date.now(), dt = patrolLastT ? Math.min(0.25, (t - patrolLastT) / 1000) : 0; patrolLastT = t; return dt * radPerSec; }

  // State cho Boss Arena Dodge & Scan
  let lastBossDist = null;
  let lastBossCheckTime = Date.now();
  let bossEscapeUntil = 0;
  let bossEscapeVector = [0, 0];
  let lastArenaScanTime = 0;

  // Blacklist cho các special không tới được / timeout
  const propBlacklist = new Map(); // key -> until timestamp

  // Watchdog kiểm tra kẹt đứng yên
  let watchdog = { lastX: null, lastY: null, lastCheckAt: Date.now(), escapeUntil: 0, escapeVector: [0, 0] };

  const sampleData = {};
  const TS = 32;

  // v0.9.1: hồ sơ hiệu năng + giãn nhịp tính toán (giảm lag)
  const perf = { avg: 0, max: 0, winMax: 0, winAt: 0, calls: 0, skipped: 0, interval: 33, lastThink: 0, fps: 0, wideMs: 0, ctxAvg: 0 };
  W.__PLH_PERF = perf;
  try {
    let n = 0, t0 = performance.now();
    const raf = () => { n++; const t = performance.now(); if (t - t0 >= 1000) { perf.fps = Math.round(n * 1000 / (t - t0)); n = 0; t0 = t; } W.requestAnimationFrame(raf); };
    W.requestAnimationFrame(raf);
  } catch (_) {}

  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const safe = (fn, fallback) => { try { return fn(); } catch (_) { return fallback; } };

  panelPrefs.min = false;
  panelPrefs.hidden = safe(() => { const v = localStorage.getItem('plh_panel_hidden'); return v === null ? isIOS : v === '1'; }, isIOS);

  // ===== v0.8.2: VIỆT HOÁ (từ điển giao diện; tên Pokémon/chiêu giữ nguyên tiếng Anh) =====
  const VI_DICT = {
    // Màn hình chính
    'Rotate your device': 'Hãy xoay ngang thiết bị', 'PokéLit is played in landscape.': 'PokéLit chơi ở chế độ màn hình ngang.',
    'Survive the hordes with your partner Pokémon · free, on PC and mobile': 'Sống sót trước bầy quái cùng Pokémon đồng hành · miễn phí, trên PC và điện thoại',
    "Official website: pokelit.0d4y.cc · if anyone asks you to pay, it isn't us": 'Trang chính thức: pokelit.0d4y.cc · nếu ai đòi bạn trả tiền, đó không phải chúng tôi',
    'Log in': 'Đăng nhập', 'Sign up': 'Đăng ký', 'Name': 'Tên', 'Password': 'Mật khẩu', 'Forgot your password?': 'Quên mật khẩu?',
    'If you linked your Gmail, tap': 'Nếu đã liên kết Gmail, hãy bấm', 'Sign in with Google': 'Đăng nhập bằng Google', 'Guide': 'Hướng dẫn',
    'Legal notice & privacy': 'Pháp lý & quyền riêng tư', 'Pick your partner directly': 'Chọn thẳng Pokémon đồng hành', 'Your personality is…': 'Tính cách của bạn là…',
    'Your partner:': 'Bạn đồng hành:', "Let's go together!": 'Cùng đi nào!', 'Choose another': 'Chọn con khác', 'Choose your partner': 'Chọn Pokémon đồng hành',
    'The starters from every region, plus two more friends.': 'Các Pokémon khởi đầu của mọi vùng, thêm hai người bạn nữa.', 'Back': 'Quay lại', 'Choose': 'Chọn',
    'Join · link your account': 'Tham gia · liên kết tài khoản', 'Season pass': 'Thẻ mùa', 'Your collection': 'Bộ sưu tập của bạn',
    'Gems from the rift legendaries': 'Đá quý từ huyền thoại trong rift', 'Upgrades': 'Nâng cấp', 'Make every run stronger': 'Mạnh hơn ở mọi trận',
    '9 regions · Pokémon and shinies': '9 vùng · Pokémon và shiny', 'Multiplayer': 'Chơi nhiều người', 'Rooms, Plaza, friends and clubs': 'Phòng, Quảng trường, bạn bè và câu lạc bộ',
    '# ONLINE': '# ĐANG CHƠI', 'Play': 'Chơi', 'Enter the dungeon': 'Vào hầm ngục', 'Mega of the week': 'Mega của tuần', 'Demonic': 'Quỷ hoá', 'One of a kind': 'Có một không hai',
    'PC Box': 'Hộp PC', 'Duplicates and star ranks': 'Bản trùng và hạng sao', 'Missions': 'Nhiệm vụ', 'Missions, achievements and profile': 'Nhiệm vụ, thành tựu và hồ sơ',
    'Friends': 'Bạn bè', 'Play in a group, up to 4': 'Chơi nhóm, tối đa 4 người', 'Leaderboard': 'Bảng xếp hạng', 'Who survives longest': 'Ai sống sót lâu nhất',
    "What's new": 'Có gì mới', 'Support': 'Ủng hộ', 'Install': 'Cài đặt app', 'Log out': 'Đăng xuất', 'Legal notice': 'Thông tin pháp lý', 'Close': 'Đóng',
    'Afraid of losing your account?': 'Sợ mất tài khoản?', 'Link your Gmail: if you ever forget your password, tap': 'Liên kết Gmail: nếu quên mật khẩu, hãy bấm',
    "and it's the same account, with all your progress.": 'và vẫn là tài khoản đó, giữ nguyên tiến trình.', 'Link my Gmail': 'Liên kết Gmail', 'Not now': 'Để sau',
    "Don't ask again": 'Đừng hỏi lại', 'Support the project': 'Ủng hộ dự án', 'Settings': 'Cài đặt', 'Fan project': 'Dự án của người hâm mộ',
    'is a game made by fans,': 'là game do người hâm mộ làm,', 'free and non-profit': 'miễn phí và phi lợi nhuận', 'Official website': 'Trang chính thức',
    'Third-party content': 'Nội dung bên thứ ba', 'Sprites from': 'Hình ảnh từ', 'Contact and content removal': 'Liên hệ và gỡ nội dung', 'Source code:': 'Mã nguồn:',
    'Based on': 'Dựa trên', 'Privacy': 'Quyền riêng tư', 'Delete my account and my game': 'Xoá tài khoản và dữ liệu game',
    'A Pokémon survival game, free in your browser and on mobile.': 'Game sinh tồn Pokémon, miễn phí trên trình duyệt và điện thoại.', 'Loading…': 'Đang tải…',
    'Survive the hordes with your Pokémon partner': 'Sống sót trước bầy quái cùng Pokémon đồng hành', 'Press to start': 'Bấm để bắt đầu',
    'Choose your nickname': 'Chọn biệt danh', 'Save nickname': 'Lưu biệt danh', 'Club': 'Câu lạc bộ', 'Go to the room': 'Vào phòng', 'Add friend': 'Kết bạn',
    'Play with other trainers: rooms, the Plaza, friends and clubs.': 'Chơi cùng huấn luyện viên khác: phòng, Quảng trường, bạn bè và câu lạc bộ.',
    'Public rooms': 'Phòng công khai', 'Quick match': 'Ghép trận nhanh', 'Create a room': 'Tạo phòng', 'PokéLit Plaza': 'Quảng trường PokéLit', 'Chat': 'Trò chuyện',
    'My club': 'CLB của tôi', 'Weekly ranking': 'Xếp hạng tuần', 'Find a club': 'Tìm CLB', 'LIVE': 'TRỰC TIẾP', 'Stop watching': 'Dừng xem', 'Waiting for their game…': 'Đang chờ trận của họ…',
    'Back to menu': 'Về menu', 'Room': 'Phòng', 'Menu': 'Menu', 'Leave the room': 'Rời phòng', 'Invite friends': 'Mời bạn', 'No messages yet. Say hi!': 'Chưa có tin nhắn. Chào một câu nhé!',
    'Send': 'Gửi', 'Start game': 'Bắt đầu', 'Mega Evolutions': 'Tiến hoá Mega', 'Demonic Forms': 'Dạng Quỷ', 'Grimoire': 'Sách phép', 'Clear filter': 'Xoá bộ lọc',
    'Players': 'Người chơi', 'Online': 'Trực tuyến', 'Game': 'Trò chơi', 'Events': 'Sự kiện', 'Codes': 'Mã', 'Plaza': 'Quảng trường', 'Trades': 'Trao đổi', 'Stats': 'Thống kê',
    'Account suspended': 'Tài khoản bị khoá', 'This account has been suspended.': 'Tài khoản này đã bị khoá.', 'Maintenance': 'Bảo trì',
    'We are updating PokéLit. Come back in a bit.': 'PokéLit đang cập nhật. Quay lại sau ít phút nhé.', 'Retry': 'Thử lại', 'Achievements': 'Thành tựu', 'Profile': 'Hồ sơ',
    'Join': 'Tham gia', 'No, thanks': 'Không, cảm ơn', 'Connecting…': 'Đang kết nối…', 'Global': 'Toàn cầu', 'Actions': 'Hành động', 'People': 'Mọi người', 'Look': 'Ngoại hình',
    'Emotes': 'Biểu cảm', 'Quick chat': 'Chat nhanh', 'Together': 'Cùng nhau', 'Player': 'Người chơi', 'Your status': 'Trạng thái của bạn', 'Everyone': 'Mọi người',
    'Tap someone to interact.': 'Chạm vào ai đó để tương tác.', 'Trade': 'Trao đổi', 'You give': 'Bạn đưa', 'Your duplicates and shinies': 'Bản trùng và shiny của bạn',
    'You received': 'Bạn nhận được', 'Great!': 'Tuyệt!', 'Unsaved changes': 'Thay đổi chưa lưu', 'Undo': 'Hoàn tác', 'Redo': 'Làm lại', 'Before': 'Trước', 'Reset': 'Đặt lại',
    'Saved outfits': 'Trang phục đã lưu', 'Wardrobe': 'Tủ đồ', 'Random': 'Ngẫu nhiên', 'Cancel': 'Huỷ', 'Save': 'Lưu', 'Buy and save': 'Mua và lưu', 'Total': 'Tổng',
    'Your coins': 'Tiền của bạn', 'Buy': 'Mua', 'Fight!': 'Chiến!', 'Tap the screen to skip': 'Chạm màn hình để bỏ qua', 'Press Space to skip': 'Bấm Space để bỏ qua',
    'Sort': 'Sắp xếp', 'Rank up all': 'Nâng hạng tất cả', 'No Pokémon matches your search.': 'Không có Pokémon nào khớp.', 'IV gems found': 'Đá IV đã tìm thấy',
    'Transfer IV': 'Chuyển IV', 'Transfer': 'Chuyển', 'Choose the region': 'Chọn vùng', 'Auto level': 'Tự lên cấp', 'Auto item': 'Tự chọn đồ',
    'Each Pokémon has its own upgrades: they only count when you play with it.': 'Mỗi Pokémon có nâng cấp riêng: chỉ có tác dụng khi bạn chơi bằng nó.',
    'Buy 1': 'Mua 1', 'Buy 5': 'Mua 5', 'Continue': 'Tiếp tục', 'Level': 'Cấp', 'Choose a reward': 'Chọn phần thưởng', 'Reroll (': 'Đổi thẻ (', 'Bond!': 'Ghép chiêu!',
    'Bonded moves fire at the same time and take a single slot': 'Chiêu đã ghép bắn cùng lúc và chỉ chiếm một ô',
    'Auto bond': 'Tự ghép chiêu', 'Two level-10 moves bond by themselves, with no screen and no pause.': 'Hai chiêu cấp 10 tự ghép với nhau, không hiện màn hình, không dừng game.',
    'Forget a move': 'Quên một chiêu', 'Keep all moves': 'Giữ mọi chiêu', 'choose': 'chọn', 'forget': 'quên', 'keep all': 'giữ hết', "Don't offer this again": 'Đừng đề nghị lại',
    "Kecleon's shop": 'Cửa hàng Kecleon', 'One item per run · Your PokéCoins:': 'Một món mỗi trận · PokéCoin của bạn:', 'Keep it for the whole run': 'Giữ suốt trận',
    'Leave': 'Rời đi', 'An item!': 'Một món đồ!', 'You can only hold one': 'Chỉ được giữ một món', 'Pause': 'Tạm dừng', 'move ·': 'di chuyển ·', 'pause': 'tạm dừng',
    'Drag your finger to move · moves fire on their own': 'Kéo ngón tay để di chuyển · chiêu tự bắn',
    "Group game: the game keeps running while you're here.": 'Trận nhóm: game vẫn chạy khi bạn ở đây.', 'Leave the rift': 'Rời rift', 'Quit run': 'Bỏ trận', 'You fell…': 'Bạn đã gục…',
    'Share in chat': 'Chia sẻ lên chat', 'Here!': 'Ở đây!', 'Help!': 'Cứu với!', 'Rift!': 'Rift!', "Let's go!": 'Đi thôi!', 'Wait': 'Chờ đã', 'Demonic forms': 'Dạng Quỷ',
    'Gacha tickets · opens the gacha': 'Vé gacha · mở gacha', 'Saved in the cloud': 'Đã lưu trên mây', 'Notifications': 'Thông báo', 'Sound': 'Âm thanh',
    'Install the app': 'Cài ứng dụng', 'Fullscreen': 'Toàn màn hình', 'More options': 'Thêm tuỳ chọn', 'Search settings': 'Tìm trong cài đặt', 'Clear': 'Xoá',
    'Write a message…': 'Viết tin nhắn…', 'Search': 'Tìm', 'Region': 'Vùng', 'Type': 'Hệ', 'Show': 'Hiện', 'Search your Pokémon': 'Tìm Pokémon của bạn',
    'Previous box': 'Hộp trước', 'Next box': 'Hộp sau', 'Click to speed up': 'Bấm để tăng tốc', 'Turn everything off': 'Tắt hết', 'Search powers…': 'Tìm sức mạnh…',
    'Runs': 'Số trận', 'Best time': 'Thời gian tốt nhất', 'Best level': 'Cấp cao nhất', 'Defeated': 'Đã hạ',
    // Cài đặt
    'Screen': 'Màn hình', 'Graphics': 'Đồ hoạ', 'Controls': 'Điều khiển', 'Account': 'Tài khoản', 'About': 'Giới thiệu', 'Language': 'Ngôn ngữ',
    'The game reloads when you change it.': 'Game sẽ tải lại khi bạn đổi.', 'Level-ups': 'Lên cấp', 'Auto level on from the start': 'Bật tự lên cấp từ đầu trận',
    'Quick level-ups': 'Lên cấp nhanh', 'Offer to forget moves': 'Đề nghị quên chiêu', 'Run': 'Trận đấu', 'Keep playing in the background': 'Tiếp tục chạy nền',
    'Moves': 'Chiêu thức', 'Dash in place': 'Lướt tại chỗ', 'Scenes': 'Cảnh phim', 'Skip cinematics': 'Bỏ qua cảnh phim', 'Skip pull animations': 'Bỏ hiệu ứng quay gacha',
    'Shop': 'Cửa hàng', 'Keep the shop item for the whole run': 'Giữ đồ mua ở shop suốt trận', 'Restore defaults': 'Khôi phục mặc định', 'Music': 'Nhạc', 'Effects': 'Hiệu ứng',
    'Alerts': 'Cảnh báo', 'Mute all': 'Tắt hết âm', 'Quality': 'Chất lượng', 'Damage numbers': 'Số sát thương', 'Show FPS': 'Hiện FPS', 'Yes': 'Có', 'No': 'Không',
    'Hover (or tap) anything to see what it does.': 'Rê chuột (hoặc chạm) vào bất kỳ thứ gì để xem tác dụng.', 'Free slot': 'Ô trống', 'Extra slot': 'Ô thêm', 'No item': 'Chưa có đồ',
    // Chỉ số / thẻ lên cấp
    'Vigor': 'Sinh lực', 'Power': 'Sức mạnh', 'Sprint': 'Tốc chạy', 'Reflexes': 'Phản xạ', 'Armor': 'Giáp', 'Synthesis': 'Quang hợp', 'Magnet': 'Nam châm',
    'Learning': 'Học hỏi', 'Sitrus Berry': 'Quả Sitrus', 'Upgrade': 'Nâng cấp', 'New': 'Mới',
    '+15 max HP (and heals it).': '+15 máu tối đa (và hồi luôn phần đó).', '+10% damage with every move.': '+10% sát thương cho mọi chiêu.', '+7% movement speed.': '+7% tốc độ di chuyển.',
    '-8% cooldown on every move.': '-8% thời gian hồi mọi chiêu.', '+4% damage reduction.': '+4% giảm sát thương nhận vào.', '+0.6 HP regenerated per second.': '+0,6 máu hồi mỗi giây.',
    '+30% experience pickup radius.': '+30% bán kính hút kinh nghiệm.', '+12% experience gained.': '+12% kinh nghiệm nhận được.', 'Restores 30% of your HP right now.': 'Hồi ngay 30% máu.',
    'Attack': 'Tấn công', 'Speed': 'Tốc độ', 'Defense': 'Phòng thủ', 'Cooldown': 'Hồi chiêu', 'Regeneration': 'Hồi máu', 'Crit': 'Chí mạng', 'Pickup': 'Nhặt', 'Experience': 'Kinh nghiệm', 'HP': 'Máu',
    // Sự kiện / thông báo trong trận
    'Level #!': 'Lên cấp #!', 'Focus Sash!': 'Focus Sash!', 'A mysterious rift has opened!': 'Một rift bí ẩn đã mở!', 'You entered the rift…': 'Bạn đã vào rift…', 'The rift threw you out…': 'Rift đã đẩy bạn ra…',
    'Boss defeated!': 'Đã hạ boss!', 'Golden hour! Double experience': 'Giờ vàng! Nhân đôi kinh nghiệm', 'Time has run out…': 'Đã hết giờ…', 'Run from Arceus! It is invincible': 'Chạy khỏi Arceus! Nó bất khả chiến bại',
    'The Judgment approaches…': 'Phán quyết đang đến…', 'Everyone is down…': 'Mọi người đều đã gục…', 'New time record!': 'Kỷ lục thời gian mới!', 'Extra slot!': 'Thêm ô chiêu!',
    'Extra slot unlocked! You can now carry 5 moves': 'Mở khoá ô thêm! Giờ bạn mang được 5 chiêu', 'Reward claimed!': 'Đã nhận thưởng!', 'Protected!': 'Được bảo vệ!',
    'Back on your feet!': 'Đứng dậy rồi!', 'The arena pulls you in!': 'Đấu trường kéo bạn vào!', 'The Titan is ENRAGED!': 'Titan đã NỔI ĐIÊN!', 'The Titan rises…': 'Titan trỗi dậy…',
    'The Titan transforms…': 'Titan biến hình…', 'The wind pushes you to the walls!': 'Gió đẩy bạn vào tường!', 'It falls on you: move!': 'Nó rơi xuống bạn: chạy đi!',
    'Clone down!': 'Hạ được bản sao!', 'The clones are gone: the Titan is vulnerable!': 'Bản sao đã hết: Titan đã yếu đi!', 'Clones! Only the real one casts a shadow': 'Bản sao! Chỉ con thật mới có bóng',
    'NOVA incoming: run to the safe circle!': 'NOVA sắp đến: chạy vào vòng an toàn!', 'NOVA incoming: there is no safe circle!': 'NOVA sắp đến: không có vòng an toàn!',
    'The Titan rift spat you out…': 'Rift Titan đã đẩy bạn ra…', 'Your loot came back with you: pick it up!': 'Chiến lợi phẩm theo bạn về: nhặt đi!', 'Leave the Titan Rift': 'Rời Rift Titan',
    'Defeat a boss': 'Hạ một boss', 'Open a locked chest': 'Mở một hòm có khoá', 'Win a rift battle': 'Thắng một trận rift', 'Follow the purple arrow: a legendary awaits inside': 'Đi theo mũi tên tím: huyền thoại đang chờ bên trong',
    'A legendary is watching you.': 'Một huyền thoại đang dõi theo bạn.', 'Today is your lucky day!': 'Hôm nay là ngày may mắn của bạn!', 'Your next shiny is close…': 'Shiny tiếp theo sắp tới…',
    'Sticky!': 'Dính!', 'Darkness falls over the throne…': 'Bóng tối phủ xuống ngai vàng…', 'Focus Sash! 2.5 s of invulnerability: get out!': 'Focus Sash! 2,5 giây bất tử: thoát ra ngay!',
    'A free pick is waiting for you in Status!': 'Có một lượt chọn miễn phí trong mục Trạng thái!', 'Play a run!': 'Chơi một trận nào!',
    'Halloween': 'Halloween', 'Fury': 'Cuồng nộ', 'Lightning': 'Tia chớp', 'Haste': 'Thần tốc',
  };
  const VI_PATTERNS = [
    [/^A wild (.+) appeared!$/, 'Một $1 hoang dã xuất hiện!'], [/^A wild shiny (.+) appeared!$/, 'Một $1 shiny hoang dã xuất hiện!'], [/^A shiny (.+) is nearby!$/, 'Có $1 shiny ở gần!'],
    [/^You got a shiny (.+)!$/, 'Bạn có được $1 shiny!'], [/^A (.+)-type horde!$/, 'Bầy quái hệ $1!'], [/^A (.+) is lost! Find it and take it to the marker$/, '$1 bị lạc! Tìm nó và đưa tới điểm đánh dấu'],
    [/^(.+) is following you! Take it to the green marker$/, '$1 đang theo bạn! Đưa nó tới điểm đánh dấu xanh'], [/^You brought (.+) home! It thanks you$/, 'Bạn đã đưa $1 về nhà! Nó cảm ơn bạn'],
    [/^A (.+) loaded with coins! Catch it before it runs away!$/, '$1 mang đầy tiền! Bắt nó trước khi nó chạy mất!'], [/^A (.+) with a ×10 ticket! Catch it before it runs away!$/, '$1 mang vé ×10! Bắt nó trước khi nó chạy mất!'],
    [/^You defeated (.+)! Grab your reward…$/, 'Bạn đã hạ $1! Nhận thưởng đi…'], [/^Golden pumpkin! \+(\d+) candy$/, 'Bí ngô vàng! +$1 kẹo'], [/^Defeat (.+) in a rift\.$/, 'Hạ $1 trong rift.'],
    [/^Level (\d+)!$/, 'Lên cấp $1!'], [/^Waiting for (.+)…$/, 'Đang chờ $1…'], [/^Achievement: (.+)!$/, 'Thành tựu: $1!'], [/^New region unlocked: (.+)!$/, 'Mở khoá vùng mới: $1!'],
    [/^NOVA in (\d+) s: run to the safe circle!$/, 'NOVA sau $1 giây: chạy vào vòng an toàn!'], [/^Level (\d+) · (.+)$/, 'Cấp $1 · $2'],
    [/^Restores (\d+)% of your HP right now\.$/, 'Hồi ngay $1% máu.'], [/^\+(\d+)% damage$/, '+$1% sát thương'], [/^Lv\.(\d+) > (\d+)$/, 'Cấp $1 > $2'],
  ];
  const viCache = new Map();
  function viTr(s) {
    if (!state.vi || typeof s !== 'string' || s.length < 2 || !/[A-Za-z]/.test(s)) return s;
    const c = viCache.get(s); if (c !== undefined) return c;
    const m = s.match(/^(\s*)([\s\S]*?)(\s*)$/), core = m[2];
    let out = VI_DICT[core];
    if (out === undefined) { const norm = core.replace(/\d+/g, '#'); const t = VI_DICT[norm]; if (t !== undefined) { const nums = core.match(/\d+/g) || []; let n = 0; out = t.replace(/#/g, () => nums[n++] ?? '#'); } }
    if (out === undefined) for (const [re, rp] of VI_PATTERNS) { if (re.test(core)) { out = core.replace(re, rp); break; } }
    const res = out === undefined ? s : m[1] + out + m[3];
    if (viCache.size > 5000) viCache.clear();
    viCache.set(s, res); return res;
  }
  // chữ vẽ trên canvas (thông báo giữa màn hình, HUD…)
  try {
    const CP = W.CanvasRenderingContext2D && W.CanvasRenderingContext2D.prototype;
    if (CP && !CP.__plhVi) {
      CP.__plhVi = true;
      for (const fn of ['fillText', 'strokeText', 'measureText']) { const o = CP[fn]; CP[fn] = function (t, ...a) { return o.call(this, typeof t === 'string' ? viTr(t) : t, ...a); }; }
    }
  } catch (_) {}
  // chữ trên trang (menu, thẻ lên cấp, cài đặt…)
  let viObsDoc = null;
  function viNode(n) {
    try {
      if (n.nodeType === 3) { const p = n.parentElement; if (!p || p.closest('script,style,textarea,[id^="plh-"],[translate="no"]')) return; const v = n.nodeValue, t = viTr(v); if (t !== v) n.nodeValue = t; return; }
      if (n.nodeType !== 1 || n.closest('[id^="plh-"],[translate="no"]')) return;
      for (const a of ['placeholder', 'title', 'aria-label']) { const v = n.getAttribute && n.getAttribute(a); if (v) { const t = viTr(v); if (t !== v) n.setAttribute(a, t); } }
      const w = document.createTreeWalker(n, NodeFilter.SHOW_TEXT | NodeFilter.SHOW_ELEMENT); let x; while ((x = w.nextNode())) { if (x.nodeType === 3) viNode(x); else for (const a of ['placeholder', 'title', 'aria-label']) { const v = x.getAttribute(a); if (v) { const t = viTr(v); if (t !== v) x.setAttribute(a, t); } } }
    } catch (_) {}
  }
  function ensureVi() {
    if (!state.vi || !document.body || viObsDoc === document.body) return;
    viObsDoc = document.body;
    viNode(document.body);
    // v0.9.1: gom thay đổi DOM và dịch theo lô (trước đây dịch ngay từng thay đổi, kể cả số đếm HUD đổi mỗi khung hình)
    const pend = new Set(); let sched = false;
    const NUMERIC = /^[\s\d.,:%+\-×x/·]*$/;
    const flush = () => {
      sched = false; let n = 0;
      for (const node of pend) { pend.delete(node); if (node.isConnected !== false) viNode(node); if (++n >= 300) break; }
      if (pend.size) { sched = true; setTimeout(flush, 80); }
    };
    new MutationObserver(muts => {
      for (const mu of muts) {
        if (mu.type === 'characterData') { const v = mu.target.nodeValue; if (!v || v.length < 2 || NUMERIC.test(v)) continue; pend.add(mu.target); }
        else if (mu.type === 'attributes') pend.add(mu.target);
        else mu.addedNodes.forEach(nd => pend.add(nd));
      }
      if (!sched && pend.size) { sched = true; setTimeout(flush, 120); }
    }).observe(document.body, { childList: true, subtree: true, characterData: true, attributes: true, attributeFilter: ['placeholder', 'title', 'aria-label'] });
  }
  setInterval(ensureVi, 400);
  // ===== hết phần Việt hoá =====


  // ===== v0.8.2: HỌC TỪ NGƯỜI CHƠI (bắt chước cách bạn tự chơi khi tắt bot) =====
  // v0.8.2: bộ nhớ học lớn — ghi TOÀN BỘ mẫu vào IndexedDB (hàng trăm MB), chia theo giai đoạn trận
  const LEARN_KEY = 'plh_learn_v1', CARDS_KEY = 'plh_learn_cards';
  const PHASES = ['đầu trận (<5p)', 'giữa (5–15p)', 'sau (15–30p)', 'cuối (>30p)', 'trong rift'];
  const POOL_MAX = isIOS ? 4000 : 7000;
  const phaseOf = (gameT, inArena) => inArena ? 4 : gameT < 300 ? 0 : gameT < 900 ? 1 : gameT < 1800 ? 2 : 3;
  const learn = { pools: [[], [], [], [], []], seen: [0, 0, 0, 0, 0], cards: {}, total: 0, runMoves: 0, ready: false, rawBuf: [] };
  try { learn.cards = JSON.parse(localStorage.getItem(CARDS_KEY) || 'null') || {}; } catch (_) {}
  Object.defineProperty(learn, 'moves', { get() { return { length: learn.total }; } });
  let learnDirty = false, learnLastRec = 0, learnLastSave = Date.now(), learnCache = { at: 0, prob: null, conf: 0 };
  let learnDB = null;
  const idbReq = (r) => new Promise((ok, no) => { r.onsuccess = () => ok(r.result); r.onerror = () => no(r.error); });
  function poolAdd(ph, f) {
    const pool = learn.pools[ph]; learn.seen[ph]++;
    if (pool.length < POOL_MAX) pool.push(f);
    else { const j = Math.floor(Math.random() * learn.seen[ph]); if (j < POOL_MAX) pool[j] = f; }
  }
  (async () => {
    try {
      const open = indexedDB.open('plh_learn', 1);
      open.onupgradeneeded = () => { const db = open.result; if (!db.objectStoreNames.contains('raw')) db.createObjectStore('raw', { autoIncrement: true }); if (!db.objectStoreNames.contains('meta')) db.createObjectStore('meta'); };
      learnDB = await idbReq(open);
      const meta = await idbReq(learnDB.transaction('meta').objectStore('meta').get('state'));
      if (meta && Array.isArray(meta.pools)) { learn.pools = meta.pools.map(p => p.map(q => q.map(v => v / 100))); learn.seen = meta.seen || learn.seen; learn.total = meta.total || 0; }
      // chuyển dữ liệu cũ (bản 0.8.0, localStorage) sang kho mới
      const old = safe(() => JSON.parse(localStorage.getItem(LEARN_KEY) || 'null'), null);
      if (old && Array.isArray(old.moves) && old.moves.length) {
        for (const m of old.moves) { const ph = m[26] ? 4 : 3; poolAdd(ph, m.slice(0, 28)); learn.total++; }
        if (old.cards && !Object.keys(learn.cards).length) learn.cards = old.cards;
        localStorage.removeItem(LEARN_KEY); learnDirty = true;
      }
    } catch (e) { console.warn(TAG, 'IndexedDB không dùng được, chỉ học trong phiên này', e); }
    learn.ready = true; saveLearn(true);
  })();
  async function saveLearn(force) {
    if (!learnDirty && !force) return;
    if (!force && Date.now() - learnLastSave < 10000) return;
    learnLastSave = Date.now(); learnDirty = false;
    try { localStorage.setItem(CARDS_KEY, JSON.stringify(learn.cards)); } catch (_) {}
    if (!learnDB || !learn.ready) return;
    try {
      const tx = learnDB.transaction(['raw', 'meta'], 'readwrite');
      if (learn.rawBuf.length) { tx.objectStore('raw').add({ at: Date.now(), s: learn.rawBuf.map(q => q.map(v => Math.round(v * 100))) }); learn.rawBuf = []; }
      tx.objectStore('meta').put({ pools: learn.pools.map(p => p.map(q => q.map(v => Math.round(v * 100)))), seen: learn.seen, total: learn.total }, 'state');
    } catch (e) { console.warn(TAG, 'Lưu dữ liệu học lỗi', e); }
  }
  async function clearLearn() {
    learn.pools = [[], [], [], [], []]; learn.seen = [0, 0, 0, 0, 0]; learn.cards = {}; learn.total = 0; learn.rawBuf = [];
    try { localStorage.removeItem(CARDS_KEY); if (learnDB) { const tx = learnDB.transaction(['raw', 'meta'], 'readwrite'); tx.objectStore('raw').clear(); tx.objectStore('meta').clear(); } } catch (_) {}
  }
  async function exportLearn() {
    let raw = [];
    try { if (learnDB) raw = await idbReq(learnDB.transaction('raw').objectStore('raw').getAll()); } catch (_) {}
    const data = { v: 1, at: new Date().toISOString(), total: learn.total, seen: learn.seen, cards: learn.cards, raw };
    const blob = new Blob([JSON.stringify(data)], { type: 'application/json' }), url = URL.createObjectURL(blob);
    const a = document.createElement('a'); a.href = url; a.download = `pokelit-hoc-${Date.now()}.json`; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 2000);
  }
  async function importLearn(file) {
    const d = JSON.parse(await file.text()); let n = 0;
    for (const ch of d.raw || []) for (const q of ch.s || []) { const f = q.map(v => v / 100); poolAdd(f[28] ?? 0, f.slice(0, 28)); learn.total++; n++; learn.rawBuf.push(f); if (learn.rawBuf.length >= 2000) { learnDirty = true; await saveLearn(true); } }
    for (const [k, v] of Object.entries(d.cards || {})) { const e = learn.cards[k] || (learn.cards[k] = { o: 0, c: 0 }); e.o += v.o || 0; e.c += v.c || 0; }
    learnDirty = true; await saveLearn(true); return n;
  }
  const r2 = v => Math.round(v * 100) / 100;
  // đặc trưng: 8 hướng quái, 8 hướng đạn, 8 hướng đồ rơi, %máu, số quái gần, đang ở rift
  function learnFeatures(ctx) {
    const f = [];
    for (let i = 0; i < 8; i++) f.push(r2(Math.log1p(Math.min(6, sectorThreat[i]))));
    for (let i = 0; i < 8; i++) f.push(r2(Math.log1p(Math.min(6, sectorShots[i]))));
    for (let i = 0; i < 8; i++) f.push(r2(Math.log1p(Math.min(6, sectorLoot[i]))));
    const me = ctx.me, hp = (me.hp || 0) / Math.max(1, me.maxHp || 1);
    const near = ctx.enemies.filter(e => Math.hypot(e.x - me.x, e.y - me.y) < 150).length;
    f.push(r2(hp), r2(Math.min(1, near / 10)), ctx.inArena ? 1 : 0);
    return f;
  }
  const dirOfVec = (x, y) => Math.hypot(x, y) < 0.25 ? 8 : ((Math.round(Math.atan2(y, x) / (Math.PI / 4)) % 8) + 8) % 8;
  function learnRecord(P, v) {
    try {
      if (!state.learnRec || P.Game.state !== 'playing' || (P.Coop && P.Coop.active && state.coop)) return;
      const now = Date.now(); if (now - learnLastRec < 150) return; learnLastRec = now;
      const ctx = makeCtx(P); if (!ctx || !ctx.me) return;
      const f = learnFeatures(ctx); f.push(dirOfVec(v[0] || 0, v[1] || 0));
      const ph = phaseOf(ctx.gameT || 0, ctx.inArena);
      poolAdd(ph, f); learn.rawBuf.push(f.concat([ph])); learn.total++; learn.runMoves++;
      learnDirty = true; saveLearn(false);
    } catch (_) {}
  }
  const LW = [];
  for (let i = 0; i < 8; i++) LW.push(1); for (let i = 0; i < 8; i++) LW.push(1.5); for (let i = 0; i < 8; i++) LW.push(0.8); LW.push(2, 0.8, 3);
  // k láng giềng gần nhất, có xoay 8 hướng để học được cả tình huống đối xứng
  function learnPolicy(ctx) {
    const now = Date.now();
    if (now - learnCache.at < (perf.avg > 6 ? 700 : 400)) return learnCache;
    learnCache = { at: now, prob: null, conf: 0 };
    if (!state.learnUse) return learnCache;
    const ph = phaseOf(ctx.gameT || 0, ctx.inArena);
    let data = learn.pools[ph];
    if (data.length < 300) { const near = ph === 4 ? [3, 2] : [ph - 1, ph + 1, ph - 2, ph + 2].filter(x => x >= 0 && x < 4); for (const x of near) if (learn.pools[x].length >= 300) { data = learn.pools[x]; break; } }
    if (data.length < 300) return learnCache;
    const q = learnFeatures(ctx), K = 12, best = [];
    const n = data.length;
    let worst = 40;
    for (let r = 0; r < 8; r++) {
      for (let j = 0; j < n; j++) {
        const s0 = data[j]; let d = 0;
        for (let blk = 0; blk < 3 && d <= worst; blk++) { const w = LW[blk * 8]; for (let i = 0; i < 8; i++) { const a = q[blk * 8 + ((i + r) & 7)] - s0[blk * 8 + i]; d += w * a * a; } }
        if (d > worst) continue;
        for (let i = 24; i < 27; i++) { const a = q[i] - s0[i]; d += LW[i] * a * a; }
        if (best.length < K || d < best[best.length - 1][0]) {
          const act = s0[27] === 8 ? 8 : (s0[27] + r) & 7;
          const ent = [d, act]; let k = best.length; best.push(ent);
          while (k > 0 && best[k - 1][0] > d) { best[k] = best[k - 1]; k--; }
          best[k] = ent; if (best.length > K) best.pop();
          worst = best.length === K ? Math.min(40, best[K - 1][0]) : 40;
        }
      }
    }
    if (!best.length) return learnCache;
    const prob = new Array(9).fill(0); let tot = 0;
    for (const [d, a] of best) { const w = 1 / (Math.sqrt(d) + 0.15); prob[a] += w; tot += w; }
    for (let i = 0; i < 9; i++) prob[i] /= tot || 1;
    const meanD = best.reduce((a, b) => a + Math.sqrt(b[0]), 0) / best.length;
    learnCache = { at: now, prob, conf: Math.max(0, 1 - meanD / 1.6) };
    return learnCache;
  }
  // phân nhóm thẻ để học bạn hay chọn loại nào
  function cardClasses(o) {
    const type = String(o?.type || ''), key = String(o?.key || ''), tag = String(o?.tag || ''), desc = String(o?.desc || '');
    const id = key.split(':')[1] || '';
    const sup = /^Passive:|no hace da|deals no damage|no damage|lower accuracy|it affects them/i.test(desc);
    const out = [];
    if (type === 'evo') out.push('evo');
    else if (type === 'stat') { out.push(key + (/^Evolves|^Evoluciona/i.test(tag) ? ':evo' : '')); }
    else if (type === 'new') out.push(sup ? 'new:hỗ trợ' : 'new:sát thương');
    else if (type === 'up') out.push(sup ? 'up:hỗ trợ' : 'up:sát thương');
    if ((type === 'new' || type === 'up') && id) out.push('chiêu:' + id);
    return out;
  }
  function learnCardPick(options, choice) {
    try {
      for (const o of options || []) for (const c of cardClasses(o)) { const e = learn.cards[c] || (learn.cards[c] = { o: 0, c: 0 }); e.o++; if (o === choice) e.c++; }
      learnDirty = true; saveLearn(true);
    } catch (_) {}
  }
  function learnCardBonus(o) {
    if (!state.learnUse) return 0;
    let b = 0;
    for (const c of cardClasses(o)) { const e = learn.cards[c]; if (e && e.o >= 3) b += (e.c / e.o - 1 / 3) * 900 * (state.learnMix ?? 0.5) * Math.min(1, e.o / 8); }
    return Math.round(b);
  }
  // ===== hết phần học =====

  function persistSettings() {
    try { localStorage.setItem('plh_settings', JSON.stringify(state)); } catch (_) {}
  }

  function logOnce(key, label, value) {
    if (logged.has(key)) return;
    logged.add(key);
    try {
      let s; try { s = JSON.stringify(value); } catch (_) { s = String(value); }
      s = String(s).slice(0, 1000);
      sampleData[key] = `${label}: ${s}`;
      console.info(`${TAG} ${label} ${s}`);
    } catch (_) { console.info(`${TAG} ${label}`); }
  }

  function plain(value) {
    try { return JSON.parse(JSON.stringify(value)); } catch (_) { return String(value); }
  }
  // v0.9.1: chỉ tạo dữ liệu mẫu khi key chưa được log (trước đây plain()/Object.keys chạy MỖI khung hình)
  function logOnceF(key, label, fn) { if (logged.has(key)) return; try { logOnce(key, label, fn()); } catch (_) { logged.add(key); } }

  function isEnemyProjectile(q, player) {
    if (!q || q.friendly === true) return false;
    const owner = q.owner, pid = player?.id;
    const ownedByPlayer = owner === player || (pid != null && (owner === pid || owner?.id === pid || q.ownerId === pid));
    return !ownedByPlayer;
  }

  function reportProjectileCounts(all, enemy) {
    if (Date.now() - lastProjectileLog >= 1000) {
      lastProjectileLog = Date.now();
      lastProjectileCount = all.length;
    }
  }

  // v0.8.8: CO-OP. Đọc đồng đội từ Coop.mates (mỗi mate: {uid,name,connected,pl:{x,y,hp,maxHp,dead,rev}}).
  function coopInfo(P, me) {
    try {
      const C = P.Coop; if (!state.coop || !C || !C.active) return { active: false, mates: [], guest: false };
      const list = (C.mates || []).filter(m => m && m.connected && m.pl && m.pl !== me && Number.isFinite(Number(m.pl.x)) && Number.isFinite(Number(m.pl.y)) && Math.hypot(Number(m.pl.x) - me.x, Number(m.pl.y) - me.y) < 6000)
        .map(m => ({ uid: m.uid, name: m.name, x: Number(m.pl.x), y: Number(m.pl.y), hp: Number(m.pl.hp) || 0, maxHp: Number(m.pl.maxHp) || 1, dead: !!m.pl.dead, rev: Number(m.pl.rev) || 0 }));
      return { active: true, isHost: !!C.isHost, guest: !C.isHost, mates: list, alive: list.filter(m => !m.dead) };
    } catch (_) { return { active: false, mates: [], guest: false }; }
  }
  // Phạt điểm đi quá xa đồng đội còn sống (giữ đội hình)
  function coopCost(ctx, x, y) {
    const cp = ctx.coop; if (!cp || !cp.active || !cp.alive || !cp.alive.length) return 0;
    let d = 1e9; for (const m of cp.alive) d = Math.min(d, Math.hypot(x - m.x, y - m.y));
    return d > 420 ? Math.min(4000, (d - 420) * 6) : 0;
  }
  // v0.9.7: Mục tiêu co-op. Game: người gục cần có đồng đội SỐNG đứng trong 56px suốt 3s (REVIVE_TIME) mới đầy thanh hồi sinh.
  // => đi tới bằng tuyến A* (không cắm đầu vào tường), tới <34px thì ĐỨNG GIỮ (#hold: tắt thoát-kẹt) đến khi hồi sinh xong.
  const coopSeen = new Map();
  const isCoopMode = m => m === 'hồi sinh đồng đội' || m === 'theo đồng đội';
  function coopRoutePick(ctx, tx, ty, key, now, d) {
    if (d <= 500) return { x: tx, y: ty };
    const rt = coarseRoute(ctx, tx, ty, key, now); let pick = null;
    for (const n of rt) { if (dist(ctx.me, n) <= 420) pick = n; else if (pick) break; }
    return pick && dist(ctx.me, pick) > 60 ? pick : { x: tx, y: ty };
  }
  function coopGoal(ctx, hp) {
    const cp = ctx.coop; if (!cp || !cp.active || !cp.mates.length) return null;
    const now = Date.now(), me = ctx.me;
    const rec = k => { try { W.__PLH_RUN_LOG?.recordCoopGoal?.(k); } catch (_) {} };
    for (const m of cp.mates) { if (coopSeen.get(m.uid) === true && !m.dead) rec('revived'); coopSeen.set(m.uid, m.dead); }
    const skip = k => (propBlacklist.get(k) || 0) > now;
    const near = ctx.enemies.filter(e => dist(me, e) < 130).length;
    // 1) HỒI SINH: điều kiện nới hơn bản cũ (trước: máu<55%, quái quanh xác >4, quái quanh mình >5 => hầu như không bao giờ cứu)
    const dead = cp.mates.filter(m => m.dead && !skip('coop:revive:' + m.uid)).sort((a, b) => dist(me, a) - dist(me, b))[0];
    if (dead && dist(me, dead) < 1500 && hp >= 0.4 && near <= 8) {
      const threat = ctx.enemies.filter(e => Math.hypot(e.x - dead.x, e.y - dead.y) < 140).length;
      if (threat <= 8) {
        const key = 'coop:revive:' + dead.uid, d = dist(me, dead), holding = goalState.key === key + '#hold';
        if (d < (holding ? 46 : 34)) {
          if (!holding) rec('holds');
          return { x: me.x, y: me.y, key: key + '#hold', mode: 'hồi sinh đồng đội', hold: true, center: { x: dead.x, y: dead.y }, holdR: 30, limMs: 9000, reason: `đứng cạnh ${dead.name || 'đồng đội'} để hồi sinh (${(dead.rev || 0).toFixed(1)}/3s)` };
        }
        const tgt = coopRoutePick(ctx, dead.x, dead.y, key, now, d);
        return { x: tgt.x, y: tgt.y, key, mode: 'hồi sinh đồng đội', limMs: 15000, final: { x: dead.x, y: dead.y }, rush: d < 350 && hp > 0.5, reason: `đi hồi sinh ${dead.name || 'đồng đội'} (${Math.round(d)}px)` };
      }
    }
    // 2) BÁM ĐỘI HÌNH: bắt đầu khi >650px, dừng khi <330px (tránh dao động), đi theo tuyến A*
    if (hp >= 0.45 && near <= 5) {
      const alive = cp.alive.filter(m => !skip('coop:follow:' + m.uid));
      if (alive.length) {
        const nm = alive.slice().sort((a, b) => dist(me, a) - dist(me, b))[0], d = dist(me, nm), key = 'coop:follow:' + nm.uid;
        if (d > (goalState.key === key ? 330 : 650)) {
          const tgt = coopRoutePick(ctx, nm.x, nm.y, key, now, d);
          return { x: tgt.x, y: tgt.y, key, mode: 'theo đồng đội', limMs: 20000, final: { x: nm.x, y: nm.y }, reason: `bám lại đồng đội (${Math.round(d)}px)` };
        }
      }
    }
    return null;
  }

  // ===== v0.8.9: Titan Rift + Boss phán xét (Arceus, phút 30) =====
  // ===== v0.9.0: Cửa hàng Kecleon (chỉ mua món trong danh sách; không có thì rời đi) =====
  const SHOP_ORDER = ['lifeorb', 'choiceband', 'choicescarf', 'quickclaw', 'leftovers', 'shellbell', 'assaultvest', 'focussash', 'kingsrock', 'rockyhelmet', 'airballoon', 'amuletcoin', 'luckyegg'];
  const SHOP_NAME = { lifeorb: 'Life Orb', choiceband: 'Choice Band', choicescarf: 'Choice Scarf', quickclaw: 'Quick Claw', leftovers: 'Leftovers', shellbell: 'Shell Bell', assaultvest: 'Assault Vest', focussash: 'Focus Sash', kingsrock: "King's Rock", rockyhelmet: 'Rocky Helmet', airballoon: 'Air Balloon', amuletcoin: 'Amulet Coin', luckyegg: 'Lucky Egg' };
  const SHOP_PRICE = { leftovers: 12000, choiceband: 16000, quickclaw: 16000, focussash: 14000, shellbell: 12000, amuletcoin: 18000, luckyegg: 10000, lifeorb: 16000, choicescarf: 14000, rockyhelmet: 10000, assaultvest: 14000, kingsrock: 14000, airballoon: 12000 };
  const shopActed = new WeakSet();
  function shopPlan(P) {
    try {
      const sh = P.Shop, st = sh && sh.stand; if (!state.shopBuy || !st || st.gone || st.bought || !Array.isArray(st.items)) return null;
      const pick = SHOP_ORDER.find(id => state.shopWant.includes(id) && st.items.includes(id)); if (!pick) return null;
      const price = Number((sh.PRICE || SHOP_PRICE)[pick]) || SHOP_PRICE[pick], coins = Number(P.DB?.save?.coins) || 0;
      if (coins < price) return null;
      return { st, pick, idx: st.items.indexOf(pick), x: Number(st.x), y: Number(st.y), price };
    } catch (_) { return null; }
  }
  // Chạy trong vòng lặp 250ms (game tạm dừng khi cửa hàng mở nên không thể đặt trong think): bấm mua món ưu tiên hoặc bấm Rời đi.
  function shopTick(P) {
    try {
      if (!state.shopBuy || !state.enabled) return;
      if (!(P.UI && P.UI.isOpen && P.UI.isOpen('scr-shop'))) return;
      const st = P.Shop && P.Shop.stand; if (!st) return;
      if (shopActed.has(st)) return; shopActed.add(st);
      const plan = shopPlan(P);
      const cards = document.querySelectorAll('#shop-cards .card');
      if (plan && cards[plan.idx] && !cards[plan.idx].classList.contains('off')) {
        console.info(`${TAG} Kecleon: mua ${SHOP_NAME[plan.pick] || plan.pick} (${plan.price})`);
        cards[plan.idx].click();
        if (W.__PLH_RUN_LOG?.recordShop) W.__PLH_RUN_LOG.recordShop('mua ' + (SHOP_NAME[plan.pick] || plan.pick));
      } else {
        console.info(`${TAG} Kecleon: không có món ưu tiên (hoặc không đủ xu) → rời đi`);
        const lv = document.getElementById('shop-leave'); if (lv) lv.click();
        if (W.__PLH_RUN_LOG?.recordShop) W.__PLH_RUN_LOG.recordShop('rời đi, không mua');
      }
    } catch (e) { console.warn(`${TAG} lỗi cửa hàng`, e); }
  }

  function titanInfo(P) {
    try {
      const Tn = P.Titan; if (!state.titanMode || !Tn) return null;
      const pt = Tn.portal;
      if (!Tn.arena && pt && Number.isFinite(Number(pt.x)) && Number.isFinite(Number(pt.y))) return { portal: { x: Number(pt.x), y: Number(pt.y) - 20, ttl: Number(pt.ttl) || 0 }, phase: 0, nova: null, clones: [], boss: null, immune: false, enrage: false, R: 0 };
      const A = Tn.arena; if (!A || typeof A.phase !== 'number' || A.phase < 1) return null;
      const Tpx = (P.Tiles?.T || 0) * (P.Sprites?.PX || 0);
      const all = P.EnemyMgr.all();
      const boss = all.find(e => e.id === A.bossId && !e.dead) || null;
      const clones = (A.clones || []).filter(c => c && !c.dead && Number.isFinite(c.x));
      const nv = A.nova && Number.isFinite(Number(A.nova.x)) ? { x: Number(A.nova.x), y: Number(A.nova.y), left: Number(A.nova.delay) - Number(A.nova.t || 0), safe: !!A.nova.safe } : null;
      return { phase: A.phase, enrage: !!A.enrage, cx: Number(A.x), cy: Number(A.y), R: (Number(A.r) || 0) * Tpx, nova: nv, boss, clones, immune: !!(boss && (boss.immune || boss.hidden)) };
    } catch (_) { return null; }
  }
  // Arceus không có getter vị trí: đọc từ lệnh vẽ (ellipse đầu tiên của hàm draw) bằng canvas giả, chỉ đọc.
  function arceusPos(J) {
    try {
      const d = J.drawable && J.drawable(); if (!d || typeof d.draw !== 'function') return null;
      let pos = null; const STOP = { stop: 1 };
      const rec = new Proxy({}, {
        get: (_, p) => {
          if (p === 'measureText') return () => ({ width: 0 });
          if (p === 'createLinearGradient' || p === 'createRadialGradient') return () => ({ addColorStop() {} });
          return (...a) => { if (!pos && (p === 'ellipse' || p === 'translate') && Number.isFinite(a[0]) && Number.isFinite(a[1])) { pos = { x: a[0], y: a[1] }; throw STOP; } };
        }, set: () => true
      });
      try { d.draw(rec); } catch (_) {}
      return pos;
    } catch (_) { return null; }
  }
  function judgeInfo(P) {
    try {
      judgeHookWorld(P); const J = P.Judgment; if (!state.judgeMode || !J || !J.active) return null;
      const sm = J.summary && J.summary(); if (!sm) return null;
      const A = arceusPos(J);
      const legends = P.EnemyMgr.all().filter(e => e.judge && !e.dead && Number.isFinite(e.x)).map(e => ({ id: e.id, x: e.x, y: e.y, r: e.r || 14, name: e.name, hp: Number(e.hp) || 0 }));
      return { time: sm.time, downs: sm.bosses, A, legends };
    } catch (_) { return null; }
  }
  // NOVA của Titan có vòng an toàn: phải đứng trong elip (|dx|<150, |dy|<112) lúc nổ, nếu không mất 85% máu.
  function titanNova(ctx) {
    const t = ctx.titan; if (!t || !t.nova || !t.nova.safe || t.nova.left > 6) return null;
    const me = ctx.me, dx = t.nova.x - me.x, dy = t.nova.y - me.y, d = Math.hypot(dx, dy);
    if (d < 35) return { v: [0, 0], mode: 'đứng trong vòng an toàn' };
    // v0.9.20: chọn hướng chạy tới vòng an toàn nhưng tránh tia / vòng nổ đang báo trước và tường trong 0.75s tới
    const spd = Math.max(40, me.baseSpd || me.spd || 90);
    let best = [dx / d, dy / d], bs = Infinity;
    for (let k = 0; k < 24; k++) {
      const a = k * Math.PI / 12, ux = Math.cos(a), uy = Math.sin(a);
      let sc = 0;
      for (const tt of [0.25, 0.5, 0.75]) {
        const px = me.x + ux * spd * tt, py = me.y + uy * spd * tt;
        if (blocked(ctx, px, py)) { sc += 6000; continue; }
        if (safe(() => ctx.hazardInside(px, py), false)) sc += 4000;
      }
      sc += Math.hypot(t.nova.x - (me.x + ux * spd * 0.75), t.nova.y - (me.y + uy * spd * 0.75));
      if (sc < bs) { bs = sc; best = [ux, uy]; }
    }
    return { v: best, mode: 'chạy vào vòng an toàn' };
  }
  // v0.9.16: né Arceus kiểu dev — tìm kiếm chùm 3 bước × 8 hướng, mô phỏng Arceus đuổi theo, tránh mép đấu trường, tiện thể áp sát huyền thoại khi đủ an toàn.
  let judgeK = -1, judgeBounds = null, judgeWorldHooked = null, judgeLast = [0, 0];
  function judgeHookWorld(P) {
    try {
      const w = P.World; if (!w || typeof w.setArena !== 'function' || judgeWorldHooked === w) return;
      const orig = w.setArena;
      w.setArena = function (arena, ...rest) {
        const res = orig.call(this, arena, ...rest);
        try { const ts = Number(w.TS) || 32; judgeBounds = arena && arena.type === 'judgment' && [arena.tx, arena.ty, arena.r].every(Number.isFinite) ? { x: arena.tx * ts + ts / 2, y: arena.ty * ts + ts / 2, r: arena.r * ts } : null; } catch (_) {}
        return res;
      };
      judgeWorldHooked = w;
    } catch (_) {}
  }
  function judgeFocus(me, j, minFromA) {
    const c = j.legends.filter(l => !j.A || Math.hypot(l.x - j.A.x, l.y - j.A.y) > minFromA);
    return c.sort((a, b) => (dist(me, a) + Math.sqrt(Math.max(0, a.hp || 0)) * 0.5) - (dist(me, b) + Math.sqrt(Math.max(0, b.hp || 0)) * 0.5))[0] || null;
  }
  function judgeFlee(ctx) {
    const j = ctx.judge; if (!j || !j.A) return null;
    const me = ctx.me, dA = Math.hypot(me.x - j.A.x, me.y - j.A.y); if (dA > 340) return null;
    const r = me.r || 12, spd = Math.max(1, me.spd || me.baseSpd || 100), aR = 30;
    const chase = Math.max(60, spd * Math.min(0.9, 0.7 + 0.008 * (Number(j.time) || 0)));
    const stride = Math.max(48, Math.min(320, spd * 0.32)), dt = stride / spd;
    const W0 = ctx.world, bnd = judgeBounds;
    const free = (x, y) => !(safe(() => W0.isWall(x, y), false) || (typeof W0.isFree === 'function' && !safe(() => W0.isFree(x, y), true)));
    const lineFree = (a, b) => [0.25, 0.5, 0.75, 1].every(t => free(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t));
    const focus = judgeFocus(me, j, 180);
    const hz = (ctx.hazards || []).filter(h => hzPending(h));
    let beam = [{ x: me.x, y: me.y, ax: j.A.x, ay: j.A.y, cost: 0, first: null, axis: judgeLast, minGap: dA - r - aR, score: 0 }], best = null;
    for (let depth = 0; depth < 3; depth++) {
      const next = [];
      for (const n of beam) for (let i = 0; i < 8; i++) {
        const axis = [Math.cos(i * Math.PI / 4), Math.sin(i * Math.PI / 4)], q = { x: n.x + axis[0] * stride, y: n.y + axis[1] * stride };
        if (!lineFree(n, q)) continue;
        let ax = n.ax, ay = n.ay, minGap = n.minGap, cost = n.cost + (1 - axis[0] * n.axis[0] - axis[1] * n.axis[1]) * 2;
        for (let k = 1; k <= 4; k++) {
          const px = n.x + (q.x - n.x) * k / 4, py = n.y + (q.y - n.y) * k / 4;
          const gap = Math.hypot(px - ax, py - ay), mv = Math.min(gap, chase * dt / 4);
          if (gap) { ax += (px - ax) / gap * mv; ay += (py - ay) / gap * mv; }
          const cl = Math.hypot(px - ax, py - ay) - r - aR; minGap = Math.min(minGap, cl);
          cost += (cl < 0 ? 3000 : Math.max(0, 90 - cl) * 1.4) / 4;
          if (hz.some(h => hzContains(h, px, py, r, 10))) cost += 400;
        }
        const margin = bnd ? bnd.r - Math.hypot(q.x - bnd.x, q.y - bnd.y) - r : Infinity, wanted = Math.max(65, Math.min(180, spd * 0.15));
        const edge = Math.max(0, wanted - margin) ** 2 * 0.035;
        const sep = Math.hypot(q.x - ax, q.y - ay) - r - aR, cont = (axis[0] * n.axis[0] + axis[1] * n.axis[1]) * 7;
        let eng = 0;
        if (focus && minGap > 110) { const bd = dist(q, focus); eng = Math.max(-110, Math.min(110, (dist(me, focus) - bd) * 0.55)) - Math.max(0, 145 - bd) * 2; }
        const score = (focus ? Math.min(260, sep) : sep) * 0.7 + Math.min(160, minGap) * 0.25 - cost - edge + cont + eng;
        next.push({ x: q.x, y: q.y, ax, ay, cost, first: n.first || q, axis, minGap, score });
      }
      next.sort((a, b) => b.score - a.score); beam = next.slice(0, 4);
      if (!beam.length) break; best = beam[0];
    }
    if (best) {
      const dx = best.first.x - me.x, dy = best.first.y - me.y, m = Math.hypot(dx, dy) || 1;
      judgeLast = [dx / m, dy / m]; judgeBeamHits++; return judgeLast;
    }
    // Không còn hướng nào thoáng: chạy thẳng ra xa Arceus (không bao giờ đi về phía nó)
    const a = Math.atan2(me.y - j.A.y, me.x - j.A.x); judgeLast = [Math.cos(a), Math.sin(a)]; return judgeLast;
  }
  let judgeBeamHits = 0;
  function specialGoal(ctx, hp) {
    const me = ctx.me;
    if (state.shopBuy && hp >= 0.5 && !ctx.titan && !ctx.judge) {
      const sp = shopPlan(W.__PL);
      if (sp && Number.isFinite(sp.x) && Number.isFinite(sp.y) && dist(me, sp) < 1600) return { x: sp.x, y: sp.y, key: 'shop:' + Math.round(sp.x / 32) + ',' + Math.round(sp.y / 32), mode: 'đi mua đồ Kecleon', reason: `đi tới Kecleon để mua ${SHOP_NAME[sp.pick]}` };
    }
    const t = ctx.titan;
    if (t && t.portal) {
      // Cổng Titan xuất hiện ngẫu nhiên (ttl 60s); vào bằng cách đứng cách cổng < 64px. Chỉ vào khi máu >= 60%.
      if (hp >= 0.6 && t.portal.ttl > 6 && dist(me, t.portal) < 1400) return { x: t.portal.x, y: t.portal.y, key: 'titan:portal', mode: 'vào cổng Titan', reason: `đi vào cổng Titan (còn ${Math.round(t.portal.ttl)}s)` };
      return null;
    }
    if (t) {
      let tgt = null, mode = 'đánh Titan', why = '';
      if (t.clones.length) {
        const c = t.clones.sort((a, b) => dist(me, a) - dist(me, b))[0], d = dist(me, c) || 1;
        tgt = { x: c.x - (c.x - me.x) / d * 120, y: c.y - (c.y - me.y) / d * 120, key: 'titan:clone' }; why = 'diệt bản sao Titan (mỗi con làm Titan mất 5% máu)';
      } else if (t.boss) {
        const R = t.immune ? 380 : (t.enrage ? 300 : 240);
        const a = Math.atan2(me.y - t.boss.y, me.x - t.boss.x) + 0.5;
        let x = t.boss.x + Math.cos(a) * R, y = t.boss.y + Math.sin(a) * R;
        if (t.R > 0) { const cd = Math.hypot(x - t.cx, y - t.cy), lim = t.R * 0.85; if (cd > lim) { x = t.cx + (x - t.cx) / cd * lim; y = t.cy + (y - t.cy) / cd * lim; } }
        tgt = { x, y, key: 'titan:orbit:' + Math.round(a * 4) }; why = t.immune ? 'Titan miễn nhiễm: giữ xa' : 'thả diều quanh Titan';
      }
      if (tgt) return { ...tgt, mode, reason: why };
    }
    const j = ctx.judge;
    if (j && j.legends.length) {
      const l = judgeFocus(me, j, 180) || judgeFocus(me, j, -1), d = dist(me, l) || 1;
      return { x: l.x - (l.x - me.x) / d * 170, y: l.y - (l.y - me.y) / d * 170, key: 'judge:' + l.id, mode: 'hạ huyền thoại', reason: `hạ ${l.name || 'huyền thoại'} (đã hạ ${j.downs})` };
    }
    return null;
  }

  // v0.9.1: cờ hành vi quái tính 1 lần theo (behavior|type|phase|state) thay vì chạy regex hàng trăm lần mỗi khung hình
  const ENEMY_FLAG_CACHE = new Map();
  function enemyFlags(e) {
    const key = (e.behavior || '') + '|' + (e.type || '') + '|' + (e.phase || '') + '|' + (e.state || '');
    let f = ENEMY_FLAG_CACHE.get(key);
    if (f) return f;
    const beh = String(e.behavior || ''), ph = String(e.phase || e.state || '').toLowerCase();
    f = {
      ranged: /ranged|fan|shooter|laser/i.test(e.behavior || e.type || ''),
      lane: /aim|windup|charge|dash/i.test(ph), fuse: /fuse/i.test(ph),
      rng: /ranged|fan|beamer/.test(beh), bf: /beamer|fan/.test(beh), bomber: /bomber/.test(beh), jumper: /jumper/.test(beh)
    };
    if (ENEMY_FLAG_CACHE.size > 400) ENEMY_FLAG_CACHE.clear();
    ENEMY_FLAG_CACHE.set(key, f);
    return f;
  }
  let worldKey = '0';
  let lastWideScan = 0, wideEvery = 0, lastEhPrune = 0, lastEvInfo = 0, cachedTraps = [];
  // v0.9.1: vệt đường đã đi (ô 64px) — để đường 'gần đích nhất' không lặp lại ngõ cụt đã quẩn quanh
  const trail = new Map(); let trailAt = 0, trailPrune = 0;
  const trailKey = (x, y) => Math.round(x / 64) + ',' + Math.round(y / 64);
  function trailTick(p, now) {
    if (now - trailAt < 500) return; trailAt = now;
    const k = trailKey(p.x, p.y), o = trail.get(k);
    if (o) { o.n++; o.t = now; } else trail.set(k, { n: 1, t: now });
    if (now - trailPrune > 5000) { trailPrune = now; for (const [kk, v] of trail) if (now - v.t > 60000) trail.delete(kk); }
  }
  const chestMem = new Map();      // v0.9.1: mọi hòm đã thấy trong ván (nhớ vĩnh viễn tới hết ván)
  const huntStats = { active: 0, opened: 0, goals: 0, wideR: 0 };
    function rememberChest(sp) {
    if (!sp || (sp.type !== 'bigchest' && sp.type !== 'chest')) return;
    const k = sp.type + ':' + (sp.id ?? (Math.round(sp.x) + ',' + Math.round(sp.y)));
    if (!chestMem.has(k)) chestMem.set(k, { sp, type: sp.type, x: sp.x, y: sp.y });
    else chestMem.get(k).sp = sp;
  }
  // quét hòm toàn map theo từng ô nhỏ (vòng tròn r=290 phủ kín ô 400x400), ưu tiên ô gần, mỗi lần tối đa ~3ms:
  // game sinh khối bản đồ rất tốn (đo ~3ms/khối trên PC), quét một phát bán kính lớn sẽ khựng hàng trăm ms.
  const SCAN_CELL = 400, SCAN_R = 290;
  const scanDone = new Set();
  let scanQueue = [], scanQueueAt = 0;
  function wideScan(P, p, now) {
    lastWideScan = now;
    if (perf.avg > 8) { wideEvery = 600; return; }   // máy đang chậm: nhường CPU
    const range = clamp(Number(state.chestRange) || 4000, 1500, 8000);
    if (!scanQueue.length && now - scanQueueAt > 1500 || now - scanQueueAt > 4000) {
      scanQueueAt = now;
      const ci = Math.round(p.x / SCAN_CELL), cj = Math.round(p.y / SCAN_CELL), n = Math.ceil(range / SCAN_CELL), arr = [];
      for (let i = -n; i <= n; i++) for (let j = -n; j <= n; j++) {
        const gx = ci + i, gy = cj + j; if (scanDone.has(gx + ',' + gy)) continue;
        const d = Math.hypot(gx * SCAN_CELL - p.x, gy * SCAN_CELL - p.y); if (d > range) continue;
        arr.push([d, gx, gy]);
      }
      arr.sort((a, b) => a[0] - b[0]); scanQueue = arr;
    }
    const t0 = performance.now();
    while (scanQueue.length) {
      const [, gx, gy] = scanQueue.shift(); scanDone.add(gx + ',' + gy);
      const list = safe(() => P.World.specialsNear(gx * SCAN_CELL, gy * SCAN_CELL, SCAN_R), []) || [];
      for (const sp of list) rememberChest(sp);
      if (performance.now() - t0 >= 3) break;
    }
    perf.wideMs = performance.now() - t0; huntStats.wideR = range; huntStats.queue = scanQueue.length; huntStats.scanned = scanDone.size;
    wideEvery = scanQueue.length ? (perf.avg > 5 ? 250 : 0) : 3000;
    if (chestMem.size > 1500) { const arr = [...chestMem].sort((a, b) => Math.hypot(a[1].x - p.x, a[1].y - p.y) - Math.hypot(b[1].x - p.x, b[1].y - p.y)).slice(0, 1000); chestMem.clear(); for (const [k, v] of arr) chestMem.set(k, v); }
  }

  function makeCtx(P) {
    const p = P.Game.player;
    if (!p) return null;
    // v0.9.2: arena/rift/Judgment nằm ở toạ độ rất xa (±160k–230k): coi là thế giới khác, đặt lại điểm tuần tra khi chuyển
    { const wk = (Math.abs(p.x) > 50000 || Math.abs(p.y) > 50000) ? Math.sign(p.x) + ',' + Math.sign(p.y) : '0'; if (wk !== worldKey) { worldKey = wk; patrolStartPos = { x: p.x, y: p.y }; } }
    if (!patrolStartPos) patrolStartPos = { x: p.x, y: p.y };
    const now = Date.now();
    trailTick(p, now);

    const enemies = safe(() => P.EnemyMgr.all(), []) || [];
    const allShots = safe(() => P.Projectiles.all(), []) || [];
    const shots = allShots.filter(q => isEnemyProjectile(q, p));
    const hazards = safe(() => { const a = P.Hazards.all; return typeof a === 'function' ? a.call(P.Hazards) : a; }, []) || [];
    let pickups = safe(() => P.Pickups.all(), []) || [];
    // v0.9.1: bỏ vật phẩm ở toạ độ vô lý (co-op có toạ độ 250k–383k) để bot không đi tới mục tiêu ảo
    { let far = false; for (let i = 0; i < pickups.length; i++) { const q = pickups[i]; if (!q || Math.abs(q.x - p.x) > 6000 || Math.abs(q.y - p.y) > 6000) { far = true; break; } } if (far) pickups = pickups.filter(q => q && Math.abs(q.x - p.x) <= 6000 && Math.abs(q.y - p.y) <= 6000); }
    // v0.9.10: chọn item — vật 'item' không nằm trong danh sách tick thì coi như không có (không đi nhặt)
    if (state.itemPick) pickups = pickups.filter(q => !q || q.kind !== 'item' || typeof q.value !== 'string' || !SHOP_ORDER.includes(q.value) || state.itemWant.includes(q.value));
    const rift = safe(() => P.Rift.rift, null);
    const arena = safe(() => P.Rift.arena, null);
    const ev = safe(() => P.Events.current, null);

    if (!logged.has('player_moves_keys') && p.moves && p.moves[0]) logOnceF('player_moves_keys', 'player.moves[0] keys:', () => ({ keys: Object.keys(p.moves[0]), sample: plain(p.moves[0]) }));
    if (allShots.length) logOnceF('projectiles', 'Projectiles.all()[0] sample:', () => plain(allShots[0]));
    if (hazards.length) logOnceF('hazard', 'Hazards.all()[0] sample:', () => plain(hazards[0]));
    if (rift) logOnceF('rift', 'Rift.rift sample:', () => plain(rift));
    if (ev) logOnceF('events', 'Events.current sample:', () => plain(ev));
    if (enemies.length) logOnceF('enemy', 'EnemyMgr.all()[0] keys/sample:', () => ({ keys: Object.keys(enemies[0]), sample: plain(enemies[0]) }));

    if (now - lastSpecialScan > 100) {
      lastSpecialScan = now;
      cachedSpecials = safe(() => P.World.specialsNear(p.x, p.y, 1400), []) || [];
      cachedTraps = [];
      // v0.8.2: BẢN ĐỒ TRÍ NHỚ - ghi lại mọi vật đặc biệt đã thấy
      for (const sp of cachedSpecials) {
        const k = sp.type + ':' + (sp.id ?? (Math.round(sp.x) + ',' + Math.round(sp.y)));
        const m = mapMem.get(k);
        if (m) { m.sp = sp; m.seen = now; } else mapMem.set(k, { sp, type: sp.type, x: sp.x, y: sp.y, seen: now });
        rememberChest(sp);
        const ts = String(sp.type || sp.kind || '').toLowerCase();
        if (ts.includes('trap') || ts.includes('spike') || ts.includes('lava') || ts.includes('fire')) cachedTraps.push({ x: sp.x ?? (sp.tx * TS + 16), y: sp.y ?? (sp.ty * TS + 16), r: sp.r || 16 });
      }
      if (mapMem.size > 600) { const arr = [...mapMem].sort((a, b) => b[1].seen - a[1].seen).slice(0, 400); mapMem = new Map(arr); }
      cachedNearestSpecial = safe(() => P.World.nearestSpecial(p.x, p.y), null) || safe(() => P.World.nearestSpecial(), null);
    }
    if ((state.chestHunt || state.chestForce) && state.chest && now - lastWideScan > wideEvery) wideScan(P, p, now);
    const specials = cachedSpecials, nearestSpecial = cachedNearestSpecial;

    reportProjectileCounts(allShots, shots);

    // v0.9.1: gắn vận tốc/cờ ngay trên đối tượng quái (không sao chép {...e} hàng trăm lần mỗi khung hình)
    const trackedEnemies = new Array(enemies.length);
    for (let i = 0; i < enemies.length; i++) {
      const e0 = enemies[i];
      const old = enemyHistory.get(e0.id);
      let vx = 0, vy = 0;
      if (old) { if (now > old.t) { const dt = (now - old.t) / 1000; vx = (e0.x - old.x) / dt; vy = (e0.y - old.y) / dt; } old.x = e0.x; old.y = e0.y; old.t = now; }
      else enemyHistory.set(e0.id, { x: e0.x, y: e0.y, t: now });
      const f = enemyFlags(e0);
      let e = e0;
      try { e0.__vx = vx; e0.__vy = vy; e0.__f = f; } catch (_) { e = { ...e0, __vx: vx, __vy: vy, __f: f }; }
      trackedEnemies[i] = e;
      if (e.behavior && !logged.has('beamer') && /beamer/.test(e.behavior)) logOnce('beamer', 'Quái beamer (đầy đủ):', plain(e));
      if (e.phase && !logged.has(`phase_${e.phase}`)) logOnce(`phase_${e.phase}`, `Enemy phase='${e.phase}' sample:`, { name: e.name, dex: e.dex, dx: e.dx, dy: e.dy, pt: e.pt, phaseT: e.phaseT });
    }
    if (now - lastEhPrune > 2000) { lastEhPrune = now; for (const [id, o] of enemyHistory) if (now - o.t > 1500) enemyHistory.delete(id); }

    // v0.9.1: tập quái/đạn gần dùng cho chấm điểm (xa quá thì ảnh hưởng không đáng kể)
    const nearE = [];
    for (let i = 0; i < trackedEnemies.length; i++) { const e = trackedEnemies[i], dx = e.x - p.x, dy = e.y - p.y; if (dx * dx + dy * dy < 640 * 640 || e.boss || e.__f.lane) nearE.push(e); }
    const nearShots = [];
    for (let i = 0; i < shots.length; i++) { const q = shots[i]; if (Math.abs(q.x - p.x) < 800 && Math.abs(q.y - p.y) < 800) nearShots.push(q); }

    // v0.8.2: sự kiện lớn đang diễn ra
    if (now - lastEvInfo > 400) {
      lastEvInfo = now;
      const evList = [];
      try { if (P.EVENT && P.EVENT.live && P.EVENT.live()) evList.push(P.EVENT.name || P.EVENT.id); } catch (_) {}
      try { if (P.Weather?.current) evList.push('Thời tiết: ' + (P.Weather.current.kind || P.Weather.current.id || P.Weather.current.name || '?')); } catch (_) {}
      try { if (P.Titan?.portal) evList.push('Cổng Titan'); if (P.Titan?.inArena) evList.push('Đánh Titan'); } catch (_) {}
      try { if (P.Judgment?.active) evList.push('Arceus Judgment'); } catch (_) {}
      try { if (P.Shop?.stand) evList.push('Shop Kecleon'); } catch (_) {}
      try { if (P.Events?.current) evList.push('Sự kiện: ' + (P.Events.current.kind || P.Events.current.type || P.Events.current.id || '?')); } catch (_) {}
      try { if (P.Events?.golden) evList.push('Golden hour'); } catch (_) {}
      eventInfo = { name: evList.join(' · '), list: evList };
    }
    let extraPickups = [];
    if (state.bigEvent) {
      const pl = safe(() => P.Pumpkins.list, null);
      if (Array.isArray(pl)) extraPickups = pl.filter(q => q && !q.dead && !q.pulled).map((q, n) => ({ id: 'pk' + n + ':' + Math.round(q.x) + ',' + Math.round(q.y), kind: q.gold ? 'pumpkinGold' : 'pumpkin', x: q.x, y: q.y }));
      if (pl && pl.length) logOnceF('pumpkin', 'Bí ngô (Pumpkins.list):', () => plain(pl[0]));
    }
    // v0.8.2: phân tích 8 hướng: quái đổ tới, đạn bay tới, đồ rơi
    sectorThreat.fill(0); sectorLoot.fill(0); sectorShots.fill(0);
    const secOf = (x, y) => ((Math.round(Math.atan2(y - p.y, x - p.x) / (Math.PI / 4)) % 8) + 8) % 8;
    for (const e of trackedEnemies) { const dd = Math.hypot(e.x - p.x, e.y - p.y); if (dd < 450) sectorThreat[secOf(e.x, e.y)] += ((e.dmg || 10) / 10) / (1 + dd / 120); }
    for (const q of shots) { const dd = Math.hypot(q.x - p.x, q.y - p.y); if (dd < 400) sectorShots[secOf(q.x, q.y)] += 1 / (1 + dd / 120); }
    for (const q of pickups) { const dd = Math.hypot(q.x - p.x, q.y - p.y); if (dd < 500) sectorLoot[secOf(q.x, q.y)] += 1 / (1 + dd / 150); }

    return {
      me: { inLiquid: !!p.inLiquid, x: p.x, y: p.y, r: p.r || 10, hp: p.hp, maxHp: p.maxHp, level: p.level, magnet: p.magnet || 78, baseSpd: p.baseSpd, spd: p.spd, moves: p.moves || p.slots || [] },
      enemies: trackedEnemies, nearE, nearShots, traps: cachedTraps, projectiles: shots, allProjectiles: allShots, hazards, pickups: extraPickups.length ? pickups.concat(extraPickups) : pickups, rift, arena, event: ev, gameT: safe(() => Number(P.Game.st.time) || 0, 0),
      specials, nearestSpecial,
      lowHp: (p.hp || 0) / Math.max(1, p.maxHp || 1) < 0.4,
      inArena: !!safe(() => P.Rift.inArena, false),
      coop: coopInfo(P, p),
      titan: titanInfo(P), judge: judgeInfo(P),
      hazardInside: (x, y) => hazards.some(h => hzPending(h) && hzContains(h, x, y, p.r || 12, 8)),
      world: P.World
    };
  }

  // v0.8.2: nước được kiểm tra theo cả thân nhân vật (tâm + 8 điểm quanh mép), không chỉ ở tâm
  const WATER_OFF = [[0, 0], [1, 0], [-1, 0], [0, 1], [0, -1], [0.7, 0.7], [-0.7, 0.7], [0.7, -0.7], [-0.7, -0.7]];
  let wetCache = new Map(), wetCacheT = 0;
  let riftRush = false;   // v0.9.13: đang lao vào rift — coi nước là đi được
  function wetAt(ctx, x, y, r) {
    if (riftRush) return false;
    const w = ctx.world; if (typeof w.isLiquid !== 'function') return false;
    const now = Date.now(); if (now - wetCacheT > 250) { wetCache = new Map(); wetCacheT = now; }
    const k = ((x / 8) | 0) + ',' + ((y / 8) | 0) + ',' + (r | 0);
    const c = wetCache.get(k); if (c !== undefined) return c;
    let v = false;
    for (const [ox, oy] of WATER_OFF) if (safe(() => w.isLiquid(x + ox * r, y + oy * r), false)) { v = true; break; }
    wetCache.set(k, v); return v;
  }
  let blkCache = new Map(), blkAt = 0;
  function blocked(ctx, x, y) {
    // v0.9.2: nhớ kết quả kiểm tra tường/nước theo ô 6px trong 150ms (hàng nghìn lần gọi mỗi lượt tính)
    const nowB = Date.now(); if (nowB - blkAt > 150) { blkCache = new Map(); blkAt = nowB; }
    const ck = ((x / 6) | 0) * 4194304 + ((y / 6) | 0);
    const hit = blkCache.get(ck); if (hit !== undefined) return hit;
    const w = ctx.world;
    const v = !!(safe(() => w.isWall(x, y), false) || wetAt(ctx, x, y, (ctx.me?.r || 12) + 4) ||
      (typeof w.isFree === 'function' && !safe(() => w.isFree(x, y), true)));
    blkCache.set(ck, v); return v;
  }

  // v0.8.7: Hazards.inside(hazard,x,y,r) cần 4 tham số -> bản cũ gọi sai nên chưa từng né vùng. Tự tính theo đúng công thức của game.
  const hzPending = h => !!h && !h.hit && (!Number.isFinite(h.delay) || !Number.isFinite(h.t) || h.t <= h.delay + 0.08);
  const hzLeft = h => (Number.isFinite(h.delay) && Number.isFinite(h.t)) ? h.delay - h.t : 9;
  function hzContains(h, x, y, pr, m) {
    const hx = Number(h.x), hy = Number(h.y); if (!Number.isFinite(hx) || !Number.isFinite(hy)) return false;
    if (h.kind === 'beam' || (h.len != null && h.angle != null)) {
      const ang = Number(h.angle) || 0, len = Number(h.len) || 360, w = Number(h.w) || 20, dx = x - hx, dy = y - hy;
      const al = dx * Math.cos(ang) + dy * Math.sin(ang), pp = -dx * Math.sin(ang) + dy * Math.cos(ang);
      return al >= -pr - m && al <= len + pr + m && Math.abs(pp) <= w / 2 + 0.6 * pr + m;
    }
    return Math.hypot(x - hx, y - hy) < (Number(h.r) || 48) + 0.6 * pr + m;
  }
  const hzSeen = new WeakSet();
  function hazardEscape(ctx) {
    const me = ctx.me, pr = me.r || 12;
    const hs = (ctx.hazards || []).filter(hzPending); if (!hs.length) return null;
    const gm = ctx.coop?.guest ? 10 : 0, inside = hs.filter(h => hzContains(h, me.x, me.y, pr, 6 + gm)); if (!inside.length) return null;
    const left = Math.min(...inside.map(hzLeft)); if (left > 2.2) return null;
    let best = null, bs = -1e9, bk = -1;
    for (let k = 0; k < 24; k++) {
      const a = k * Math.PI / 12, dx = Math.cos(a), dy = Math.sin(a); let exit = null;
      for (let d = 8; d <= 360; d += 8) {
        const x = me.x + dx * d, y = me.y + dy * d;
        if (safe(() => ctx.world.isWall(x, y), false) || (typeof ctx.world.isFree === 'function' && !safe(() => ctx.world.isFree(x, y), true))) break;
        if (!hs.some(h => hzContains(h, x, y, pr, 16 + gm))) { exit = d; break; }
      }
      if (exit == null) continue;
      const ex = me.x + dx * exit, ey = me.y + dy * exit;
      let sc = -exit - ctx.enemies.filter(e => Math.hypot(e.x - ex, e.y - ey) < 45).length * 50 - (wetAt(ctx, ex, ey, pr) ? 40 : 0) + (hazEscK === k ? 25 : 0);
      if (sc > bs) { bs = sc; best = [dx, dy]; bk = k; }
    }
    if (!best) return null;
    hazEscK = bk;
    for (const h of inside) if (!hzSeen.has(h)) { hzSeen.add(h); if (W.__PLH_RUN_LOG?.recordHazard) W.__PLH_RUN_LOG.recordHazard(h.kind || 'zone'); }
    return best;
  }
  let hazEscK = -1;

  function wallMob(ctx, x, y) {
    const k = (x | 0) + ',' + (y | 0), c = ctx.mobC && ctx.mobC.get(k); if (c !== undefined) return c;
    let n = 0; for (let i = 0; i < 8; i++) { const a = i * Math.PI / 4; if (!blocked(ctx, x + Math.cos(a) * 32, y + Math.sin(a) * 32)) n++; }
    if (ctx.mobC) ctx.mobC.set(k, n); return n;
  }
  function scorePoint(ctx, x, y, tp = 0.4) {
    let cost = blocked(ctx, x, y) ? 10000 : 0;
    const mr = ctx.me.r;
    const traps = ctx.traps;
    if (traps) for (let i = 0; i < traps.length; i++) { const t = traps[i]; const d = Math.hypot(x - t.x, y - t.y) - t.r - mr; if (d < 30) cost += 15000 * Math.exp(-Math.max(0, d) / 12); }

    if (state.dodge && !ctx.force) {
      const rs = ctx.rushScale || 1, lowHp = ctx.lowHp;
      const list = ctx.nearE || ctx.enemies;
      for (let i = 0; i < list.length; i++) {
        const e = list[i], f = e.__f || enemyFlags(e), er = e.r || 10, spd = e.spd || 0;
        const ex = e.x + (e.__vx || 0) * tp, ey = e.y + (e.__vy || 0) * tp;
        const dEx = Math.hypot(x - ex, y - ey);
        // v0.8.2: phạt cứng khi điểm dự đoán chạm thân quái (cùng thời điểm)
        const touch = dEx - (er + mr + 10);
        if (touch < 0) cost += rs * 9000 * Math.min(4, ((e.dmg || 10) / 10)) * (1 - touch / 40);

        // Trọng số nguy hiểm quái = (dmg/10) * (spd/55) * (bắn xa ? 1.5 : 1); >=3 thì giữ khoảng cách 120px
        const threatWeight = ((e.dmg || 10) / 10) * ((e.spd || 55) / 55) * (f.ranged ? 1.5 : 1.0);
        const minKeepDist = threatWeight >= 3.0 ? 120 : 28;
        const safeRadius = er + mr + minKeepDist + spd * 0.25;
        const d = Math.max(0, dEx - safeRadius);
        cost += rs * ((e.boss ? 12000 : 6000) * threatWeight) / (d * d + 16);

        if (f.lane) {
          let dx = e.dx || e.__vx || (ctx.me.x - e.x), dy = e.dy || e.__vy || (ctx.me.y - e.y);
          const len = Math.hypot(dx, dy) || 1;
          dx /= len; dy /= len;
          const laneLen = Math.max(260, (e.spd || 80) * 1.0 + 120);
          const laneWidth = (e.r || 12) * 2 + mr + 16;
          const px = x - e.x, py = y - e.y;
          const proj = clamp(px * dx + py * dy, 0, laneLen);
          const perp = Math.hypot(px - proj * dx, py - proj * dy);
          if (perp < laneWidth) cost += 12000 * (1 - perp / laneWidth);
        }

        // v0.8.2: quái bắn xa -> giữ ngoài tầm; quái tự nổ (fuse) -> tránh xa; quái nhảy (jumper) -> giữ khoảng
        if (f.rng) {
          const rg = Number(e.def?.range) || (/beamer/.test(e.behavior || '') ? 260 : 190);
          if (dEx < rg + 15) cost += rs * (f.bf ? 1600 : 900) * (1 - dEx / (rg + 15));
        }
        if (f.fuse || (f.bomber && dEx < 90)) {
          if (dEx < 120) cost += 20000 * (1 - dEx / 120);
        }
        if (f.jumper) {
          const jr = e.jump ? 120 : 85;
          if (dEx < jr) cost += (e.jump ? 9000 : 2500) * (1 - dEx / jr);
        }
        if (lowHp && dEx < 160) cost += rs * 1500 * (1 - dEx / 160) * Math.min(3, threatWeight);

        if (e.hbDelay > 0) {
          const hbRange = (e.def && e.def.range) || ((e.r || 12) * 3);
          const dHb = Math.hypot(x - e.x, y - e.y);
          if (dHb < hbRange + mr + 10) cost += 15000 / (dHb + 1);
        }
      }

      const sl = ctx.nearShots || ctx.projectiles;
      for (let i = 0; i < sl.length; i++) {
        const q = sl[i];
        // v0.8.2: so vị trí đạn ở CÙNG thời điểm với điểm đang xét
        const life = Number(q.life);
        if (Number.isFinite(life) && life < tp) continue;
        const qx = q.x + (q.vx || 0) * tp, qy = q.y + (q.vy || 0) * tp;
        const d = Math.hypot(x - qx, y - qy) - (q.r || 6) - mr;
        cost += 7000 * Math.exp(-Math.max(0, d) / 14) + 600 * Math.exp(-Math.max(0, d) / 40);
      }

      for (const h of ctx.hazards) {
        if (!hzPending(h)) continue;
        const left = hzLeft(h);
        if (tp > left + 0.5) continue;
        if (hzContains(h, x, y, mr, 14 + (ctx.coop?.guest ? 10 : 0))) cost += left < 0.8 ? 40000 : 16000;
        else {
          const hx = Number(h.x), hy = Number(h.y); if (!Number.isFinite(hx) || !Number.isFinite(hy)) continue;
          const d = Math.hypot(x - hx, y - hy) - (h.kind === 'beam' ? (h.w || 20) : (h.r || 48)) - mr;
          cost += 300 * Math.exp(-Math.max(0, d) / 30);
        }
      }
      cost += coopCost(ctx, x, y);
      // v0.9.16: bị dồn vào tường/cây (<=4 hướng thoát) khi quái sát bên -> ưu tiên điểm có nhiều hướng thoát hơn (như dev)
      if (ctx.wallP === undefined) {
        ctx.wallP = 8; ctx.mobC = new Map();
        const m0 = ctx.me; if ((ctx.nearE || ctx.enemies).some(e => Math.hypot(e.x - m0.x, e.y - m0.y) < (m0.r || 12) + (e.r || 10) + 140)) ctx.wallP = wallMob(ctx, m0.x, m0.y);
      }
      if (ctx.wallP <= 4) cost -= Math.max(0, wallMob(ctx, x, y) - ctx.wallP) * 350;
    }
    return cost;
  }

  function pointOnSafePath(ctx, goal) {
    // v0.8.2: chỉ loại XP khi quái mạnh đứng sát đường đi; tường để A* tự xử lý
    const dx = goal.x - ctx.me.x, dy = goal.y - ctx.me.y;
    if (blocked(ctx, goal.x, goal.y)) return false;
    for (let k = 2; k <= 10; k += 2) {
      const x = ctx.me.x + dx * k / 10, y = ctx.me.y + dy * k / 10;
      for (const e of ctx.enemies) {
        const threat = ((e.dmg || 10) / 10) * ((e.spd || 55) / 55);
        if (threat < 1.4 && !e.boss) continue;
        const ex = e.x + (e.__vx || 0) * 0.3, ey = e.y + (e.__vy || 0) * 0.3;
        const r = (e.r || 10) + ctx.me.r + 14;
        if (Math.hypot(x - ex, y - ey) < r) return false;
      }
    }
    return true;
  }

  function astarWaypoint(ctx, goal) {
    const cell = TS, me = ctx.me;
    const sx = Math.round(me.x / cell), sy = Math.round(me.y / cell);
    const gx = Math.round(goal.x / cell), gy = Math.round(goal.y / cell);
    const cacheKey = `${sx},${sy}:${gx},${gy}:${goal.mode || ''}`;
    const t00 = Date.now();
    if (pathCache.key === cacheKey && t00 - pathCache.at < 220) return pathCache.point;

    // chỉ giữ quái gần (mảng phẳng x,y,r²) cho phần phạt nguy hiểm theo ô
    const dang = [];
    if (!ctx.riftRush) for (const e of ctx.enemies) {
      const ex = e.x + (e.__vx || 0) * .4, ey = e.y + (e.__vy || 0) * .4;
      const r = (e.r || 10) + me.r + 28 + (e.spd || 0) * .25;
      if (Math.abs(ex - me.x) > 540 + r || Math.abs(ey - me.y) > 540 + r) continue;
      dang.push(ex, ey, r * r);
    }
    const K = (x, y) => (x + 200000) * 400003 + (y + 200000);
    const heap = [];
    const push = n => { let i = heap.length; heap.push(n); while (i > 0) { const pI = (i - 1) >> 1; if (heap[pI].f <= n.f) break; heap[i] = heap[pI]; i = pI; } heap[i] = n; };
    const pop = () => {
      const top = heap[0], last = heap.pop();
      if (heap.length) { let i = 0; const n = heap.length; for (;;) { let c = 2 * i + 1; if (c >= n) break; if (c + 1 < n && heap[c + 1].f < heap[c].f) c++; if (heap[c].f >= last.f) break; heap[i] = heap[c]; i = c; } heap[i] = last; }
      return top;
    };
    const start = { x: sx, y: sy, g: 0, f: Math.hypot(gx - sx, gy - sy), par: null };
    push(start);
    const costs = new Map([[K(sx, sy), 0]]);
    const dirs = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
    let found = null, iterations = 0, bestN = start, bestH = start.f + 1e-6 + (trail.get(trailKey(sx * cell + 16, sy * cell + 16))?.n ? Math.min(30, trail.get(trailKey(sx * cell + 16, sy * cell + 16)).n) * 3 : 0);

    const maxIt = goal.mode === 'tới hòm' || goal.mode === 'rương' ? 1100 : 500;   // v0.9.20: đường tới hòm được tìm sâu hơn (mục tiêu khác giữ 500)
    while (heap.length && iterations < maxIt) {
      const cur = pop();
      if (cur.g > (costs.get(K(cur.x, cur.y)) ?? Infinity) + 1e-9) continue; // mục cũ đã có đường tốt hơn
      iterations++;
      const h0 = Math.hypot(cur.x - gx, cur.y - gy);
      if (h0 <= 1.5) { found = cur; break; }
      { const tv = trail.get(trailKey(cur.x * cell + 16, cur.y * cell + 16)); const hp0 = h0 + (tv ? Math.min(30, tv.n) * 3 : 0); if (hp0 < bestH) { bestH = hp0; bestN = cur; } }

      for (let di = 0; di < 8; di++) {
        const dx = dirs[di][0], dy = dirs[di][1];
        const x = cur.x + dx, y = cur.y + dy;
        const wx = x * cell + 16, wy = y * cell + 16;
        if (Math.hypot(wx - me.x, wy - me.y) > 500 || blocked(ctx, wx, wy)) continue;
        let danger = 0;
        for (let i = 0; i < dang.length; i += 3) { const ddx = wx - dang[i], ddy = wy - dang[i + 1]; if (ddx * ddx + ddy * ddy < dang[i + 2]) danger += 40; }
        const gScore = cur.g + (dx && dy ? 1.414 : 1) + danger;
        const k = K(x, y);
        if (gScore >= (costs.get(k) ?? Infinity)) continue;
        costs.set(k, gScore);
        push({ x, y, g: gScore, f: gScore + Math.hypot(gx - x, gy - y), par: cur });
      }
    }

    // v0.9.1: không tới được hẳn (mục tiêu xa hơn vùng tìm 500px) -> đi theo nút gần đích nhất đã tìm được thay vì đâm thẳng
    const end = found || (bestN !== start ? bestN : null);
    if (!end) {
      pathCache = { key: cacheKey, at: Date.now(), point: goal, reachable: false, partial: false, route: [] };
      return goal;
    }
    const route = [];
    for (let n = end; n.par; n = n.par) route.push({ x: n.x * cell + 16, y: n.y * cell + 16 });
    const point = route.length ? route[route.length - 1] : { x: sx * cell + 16, y: sy * cell + 16 };
    pathCache = { key: cacheKey, at: Date.now(), point, reachable: !!found, partial: !found, route };
    return point;
  }

  let evCache = { obj: undefined, at: 0, txt: '' };

  // ===== v0.9.1: MỞ HÒM TOÀN MAP — không xét máu, không xét số quái (theo yêu cầu) =====
  try { W.__PLH_DBG = { get goal() { return goalState; }, get path() { return pathCache; }, get hunt() { return huntStats; }, get chests() { return chestMem; }, get us() { return us; } }; } catch (_) {}
  const hunt = { lastKey: '', nearSince: new Map(), exTarget: null, exUntil: 0, exSeq: 0, visited: new Set() };
  function approachPoint(ctx, pos, r) {
    const me = ctx.me, a0 = Math.atan2(me.y - pos.y, me.x - pos.x);
    for (let k = 0; k < 8; k++) {
      const a = a0 + (k % 2 ? 1 : -1) * Math.ceil(k / 2) * Math.PI / 4;
      const x = pos.x + Math.cos(a) * r, y = pos.y + Math.sin(a) * r;
      if (!blocked(ctx, x, y)) return { x, y };
    }
    return { x: pos.x + Math.cos(a0) * r, y: pos.y + Math.sin(a0) * r };
  }
  // đường đi thô (ô 64px, tối đa ~700 nút, ≤25ms) để vòng qua vật cản lớn khi hòm ở xa; làm mới mỗi 4s
  const coarse = { key: '', at: 0, route: [], found: false };
  // v0.9.6: ô 64px từng làm bot kẹt -> tạm coi là vật cản 45s để đường thô vòng sang chỗ khác
  const badCells = new Map();
  const badKey = (x, y) => Math.round(x / 64) + ',' + Math.round(y / 64);
  function isBad(x, y, now) { if (!badCells.size) return false; const e = badCells.get(badKey(x, y)); return !!e && e > now; }
  function markBad(x, y, now) { for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) badCells.set(badKey(x + dx * 64, y + dy * 64), now + 45000); if (badCells.size > 400) for (const [k, e] of badCells) if (e < now) badCells.delete(k); }
  const huntFails = new Map();
  // trả về true nếu hòm bị bỏ tạm (sau 3 lần lỗi); lần đầu/hai chỉ đánh dấu chỗ kẹt rồi dò đường lại
  function huntFail(me, key, now) {
    key = String(key).split('#')[0]; markBad(me.x, me.y, now); coarse.at = 0; pathCache.at = 0;
    const n = (huntFails.get(key) || 0) + 1; huntFails.set(key, n);
    W.__PLH_RUN_LOG?.recordChestEv?.(n >= 3 ? 'bỏ hòm (thất bại 3 lần)' : 'thử lại hòm (kẹt/hết giờ/không tới được)');
    if (n >= 3) { huntFails.delete(key); propBlacklist.set(key, now + 20000); return true; }   // v0.9.13: 60s → 20s để quay lại mở sớm
    return false;
  }
  const routeCache = new Map();
  function routeInfo(ctx, pos, key, now) {
    const c = routeCache.get(key); if (c && now - c.at < 10000) return c;
    const r = coarseCore(ctx, pos.x, pos.y), info = { at: now, found: r.found, len: r.len };
    routeCache.set(key, info); if (routeCache.size > 300) for (const [k, v] of routeCache) if (now - v.at > 10000) routeCache.delete(k);
    return info;
  }
  function coarseRoute(ctx, tx, ty, key, now) {
    if (coarse.key === key && now - coarse.at < 4000) return coarse.route;
    const r = coarseCore(ctx, tx, ty);
    coarse.key = key; coarse.at = now; coarse.route = r.route; coarse.found = r.found;
    return r.route;
  }
  function coarseCore(ctx, tx, ty) {
    const t0 = performance.now(), C = 64, me = ctx.me, nowT = Date.now();
    const sx = Math.round(me.x / C), sy = Math.round(me.y / C), gx = Math.round(tx / C), gy = Math.round(ty / C);
    const K = (x, y) => (x + 100000) * 200003 + (y + 100000);
    const heap = [];
    const push = n => { let i = heap.length; heap.push(n); while (i > 0) { const pI = (i - 1) >> 1; if (heap[pI].f <= n.f) break; heap[i] = heap[pI]; i = pI; } heap[i] = n; };
    const pop = () => { const top = heap[0], last = heap.pop(); if (heap.length) { let i = 0; const n = heap.length; for (;;) { let c = 2 * i + 1; if (c >= n) break; if (c + 1 < n && heap[c + 1].f < heap[c].f) c++; if (heap[c].f >= last.f) break; heap[i] = heap[c]; i = c; } heap[i] = last; } return top; };
    const start = { x: sx, y: sy, g: 0, f: Math.hypot(gx - sx, gy - sy), par: null };
    push(start);
    const costs = new Map([[K(sx, sy), 0]]);
    let found = null, best = start, bestH = start.f, it = 0;
    while (heap.length && it < 2600) {
      const cur = pop();
      if (cur.g > (costs.get(K(cur.x, cur.y)) ?? Infinity) + 1e-9) continue;
      it++;
      const h = Math.hypot(cur.x - gx, cur.y - gy);
      if (h <= 1.5) { found = cur; break; }
      if (h < bestH) { bestH = h; best = cur; }
      if ((it & 63) === 0 && performance.now() - t0 > 22) break;
      for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) {
        if (!dx && !dy) continue;
        const x = cur.x + dx, y = cur.y + dy, k = K(x, y), g = cur.g + (dx && dy ? 1.414 : 1);
        if (g >= (costs.get(k) ?? Infinity)) continue;
        if (blocked(ctx, x * C, y * C) || isBad(x * C, y * C, nowT)) continue;
        costs.set(k, g); push({ x, y, g, f: g + Math.hypot(gx - x, gy - y), par: cur });
      }
    }
    const end = found || best, route = [];
    for (let n = end; n && n.par; n = n.par) route.push({ x: n.x * C, y: n.y * C });
    route.reverse();
    perf.coarseMs = performance.now() - t0;
    let len = 0, px = me.x, py = me.y; for (const n of route) { len += Math.hypot(n.x - px, n.y - py); px = n.x; py = n.y; }
    return { route, found: !!found, len: len + Math.hypot(tx - px, ty - py) };
  }
  // v0.9.3: độ dài đường còn lại theo tuyến thô (đường vòng vẫn tính là đang tiến lại gần)
  function routeRemain(me, key, fin) {
    if (coarse.key !== key || !coarse.route.length) return null;
    const r = coarse.route; let bi = 0, bd = Infinity;
    for (let i = 0; i < r.length; i++) { const d = Math.hypot(r[i].x - me.x, r[i].y - me.y); if (d < bd) { bd = d; bi = i; } }
    let L = bd; for (let i = bi; i + 1 < r.length; i++) L += Math.hypot(r[i + 1].x - r[i].x, r[i + 1].y - r[i].y);
    return L + Math.hypot(r[r.length - 1].x - fin.x, r[r.length - 1].y - fin.y);
  }
  function chestHuntGoal(ctx, now) {
    const me = ctx.me, range = clamp(Number(state.chestRange) || 4000, 800, 8000);
    let best = null, bestScore = Infinity, active = 0;
    const seen = new Set();
    const liveKeys = new Set();
    for (const q of ctx.specials || []) if (q && (q.type === 'bigchest' || q.type === 'chest')) { const qp = xyPoint(q); if (qp) liveKeys.add(`sp:${q.type}:${q.id ?? (qp.x + ',' + qp.y)}`); }
    const cands = [];
    const markOpened = (key) => { const tr = chestTrack.get(key) || { max: 0 }; if (!tr.counted) { tr.counted = true; huntStats.opened++; W.__PLH_RUN_LOG?.recordChestEv?.('mở xong'); } chestTrack.set(key, tr); propBlacklist.set(key, now + 600000); };
    const consider = sp => {
      if (!sp || seen.has(sp)) return; seen.add(sp);
      if (sp.type !== 'bigchest' && sp.type !== 'chest') return;
      const pos = xyPoint(sp); if (!pos) return;
      const dS = dist(me, pos); if (dS > range) return;      // lọc toạ độ vô lý và quá xa
      const key = `sp:${sp.type}:${sp.id ?? (pos.x + ',' + pos.y)}`;
      const trk = chestTrack.get(key);
      if (sp.dead || sp.used) { if (trk?.held || dS < 300) markOpened(key); return; }
      if (propBlacklist.has(key) && now < propBlacklist.get(key)) return;
      // v0.9.6: hòm nhớ trong bản đồ nhưng đứng gần (<350px) mà game không còn liệt kê => đã mở/vỡ xong
      if (dS < 350 && !liveKeys.has(key) && ctx.specials) { if (trk?.held || dS < 200) markOpened(key); else propBlacklist.set(key, now + 30000); return; }   // v0.9.13: 10 phút → 30s (hòm game chưa liệt kê thì thử lại)
      if (sp.type === 'bigchest') {
        const tr = chestTrack.get(key) || { max: 0 }; const op = Number(sp.open) || 0;
        if (op > tr.max) tr.max = op; chestTrack.set(key, tr);
        if (tr.max >= 3.0 && op < 0.2) { markOpened(key); return; }   // đã mở xong
      }
      active++;
      cands.push({ sp, pos, key, dS, sc: dS - (sp.type === 'bigchest' ? 300 : 0) - ((chestTrack.get(key)?.max || 0) > 0.2 ? 250 : 0) });   // v0.9.13: hòm đã mở dở được ưu tiên quay lại
    };
    for (const sp of ctx.specials || []) consider(sp);
    for (const m of chestMem.values()) consider(m.sp);
    huntStats.active = active;
    // v0.9.6: đã cam kết hòm nào thì đi tới cùng (như cổng rift); chỉ chọn lại khi chưa có hòm cam kết
    let committed = null;
    for (const c of cands) if (String(goalState.key).startsWith(c.key)) { committed = c; break; }
    if (committed) best = committed;
    else if (cands.length) {
      cands.sort((a, b) => a.sc - b.sc);
      const t0 = performance.now();
      let bestC = null, bestV = Infinity;
      for (let i = 0; i < Math.min(3, cands.length); i++) {
        const c = cands[i];
        let v = c.sc;
        if (i === 0 || performance.now() - t0 < 40) {
          const ri = routeInfo(ctx, c.pos, c.key, now);     // độ dài đường vòng thật (không phải đường chim bay)
          v = (ri.found ? ri.len : ri.len + 3000) - (c.sp.type === 'bigchest' ? 300 : 0);
        }
        if (v < bestV) { bestV = v; bestC = c; }
      }
      best = bestC;
    }
    if (!best) return null;
    const { sp, pos, key, dS } = best;
    const spd = Math.max(40, me.baseSpd || me.spd || 90);
    const limMs = clamp(dS / (spd * 0.5) * 1000 + 8000, 12000, 120000);
    if (sp.type === 'bigchest') {
      const zoneR = Math.max(46, me.r + (sp.r || 14) + 24) - 2;
      if (dS < zoneR) {
        { const tk = chestTrack.get(key) || { max: 0 }; tk.held = true; chestTrack.set(key, tk); }
        if (goalState.key === key + '#hold' && now - goalState.since > 6000 && (Number(sp.open) || 0) < 0.3) { propBlacklist.set(key, now + 60000); return null; }
        return { goal: { x: me.x, y: me.y, weight: 2.2, mode: 'mở hòm', key: key + '#hold', hold: true, center: pos, holdR: zoneR }, reason: `đứng mở hòm to (${(Number(sp.open) || 0).toFixed(1)}/3.5s)` };
      }
      if (hunt.lastKey !== key) { hunt.lastKey = key; huntStats.goals++; }
      const ap = approachPoint(ctx, pos, 40);
      let tgt = ap;
      if (dS > 500) { const rt = coarseRoute(ctx, ap.x, ap.y, key, now); let pick = null; for (const n of rt) { if (dist(me, n) <= 420) pick = n; else if (pick) break; } if (pick && dist(me, pick) > 60) tgt = pick; }
      return { goal: { x: tgt.x, y: tgt.y, weight: 2.2, mode: 'tới hòm', key, rush: dS < 350, limMs, final: ap }, reason: `đi tới hòm to, cách ${dS.toFixed(0)}px (${active} hòm đã biết)` };
    }
    // hòm nhỏ: đứng sát để skill tự đánh vỡ; ở sát quá 5s mà chưa hết thì coi như đã vỡ
    if (dS < 70) {
      const t0 = hunt.nearSince.get(key) || now; hunt.nearSince.set(key, t0);
      if (now - t0 > 5000) { markOpened(key); hunt.nearSince.delete(key); return null; }
    }
    const ap = approachPoint(ctx, pos, 30);
    let tgt = ap;
    if (dS > 500) { const rt = coarseRoute(ctx, ap.x, ap.y, key, now); let pick = null; for (const n of rt) { if (dist(me, n) <= 420) pick = n; else if (pick) break; } if (pick && dist(me, pick) > 60) tgt = pick; }
    return { goal: { x: tgt.x, y: tgt.y, weight: 1.8, mode: 'rương', key, limMs, final: ap }, reason: `đánh vỡ hòm nhỏ, cách ${dS.toFixed(0)}px (${active} hòm đã biết)` };
  }
  // chưa biết hòm nào còn mở: đi thám hiểm sang vùng chưa tới (chỉ khi xung quanh vắng quái)
  function exploreGoal(ctx, now) {
    const me = ctx.me, range = clamp(Number(state.chestRange) || 4000, 800, 8000);
    const cellKey = (x, y) => Math.round(x / 500) + ',' + Math.round(y / 500);
    hunt.visited.add(cellKey(me.x, me.y));
    if (hunt.visited.size > 4000) hunt.visited.clear();
    if (hunt.exTarget && now < hunt.exUntil && dist(me, hunt.exTarget) > 90 && !blocked(ctx, hunt.exTarget.x, hunt.exTarget.y)) {
      return { x: hunt.exTarget.x, y: hunt.exTarget.y, weight: 1.0, mode: 'tìm hòm', key: 'explore:' + hunt.exSeq, limMs: 12000 };
    }
    let best = null, bs = -1e9;
    for (let k = 0; k < 16; k++) {
      const a = k * Math.PI / 8 + Math.random() * 0.2, R = 700;
      const x = me.x + Math.cos(a) * R, y = me.y + Math.sin(a) * R;
      if (blocked(ctx, x, y)) continue;
      if (patrolStartPos && Math.hypot(x - patrolStartPos.x, y - patrolStartPos.y) > range) continue;
      const sc = (hunt.visited.has(cellKey(x, y)) ? 0 : 1000) + Math.random() * 120;
      if (sc > bs) { bs = sc; best = { x, y }; }
    }
    if (!best) return null;
    hunt.exTarget = best; hunt.exUntil = now + 9000; hunt.exSeq++;
    return { x: best.x, y: best.y, weight: 1.0, mode: 'tìm hòm', key: 'explore:' + hunt.exSeq, limMs: 12000 };
  }
  function chooseGoal(ctx) {
    const me = ctx.me, now = Date.now();
    const near120 = ctx.enemies.filter(e => dist(me, e) < 120);
    const near150 = ctx.enemies.filter(e => dist(me, e) < 150);
    const close = ctx.enemies.filter(e => dist(me, e) < (e.r || 10) + me.r + 20);
    const urgentClose = ctx.enemies.some(e => dist(me, e) < 40);
    const hp = me.hp / Math.max(1, me.maxHp);

    const eventObj = ctx.event, eventText = (eventObj === evCache.obj && now - evCache.at < 600) ? evCache.txt : ((evCache = { obj: eventObj, at: now, txt: safe(() => JSON.stringify(eventObj || ''), '') }).txt);
    const eventTarget = eventObj?.targetId ?? eventObj?.enemyId ?? eventObj?.target?.id;

    // Meowth / Sự kiện
    const fleeing = ctx.enemies.filter(e => /meowth/i.test(e.name || '') || Number(e.dex) === 52 || /flee/i.test(e.behavior || '') || (/meowth/i.test(eventText) && eventTarget != null && String(e.id) === String(eventTarget)));
    const chase = fleeing.sort((a, b) => dist(me, a) - dist(me, b))[0];
    const crowd150 = ctx.enemies.filter(e => dist(me, e) < 150).length;
    const tkChase = !!chase && state.ticketFocus && (/ticket|vé|×10/i.test(eventText) || safe(() => W.__PL.EnemyMgr.all().find(x => x.id === chase.id)?.def?.loot === 'ticket10', false));
    if (activeChaseId != null && (now - chaseStart > (tkChase ? 30000 : 15000) || hp < (tkChase ? .45 : .5) || crowd150 > (tkChase ? 8 : 6))) { activeChaseId = null; chaseBan = now + 20000; }
    if (chase && activeChaseId == null && hp > (tkChase ? .5 : .6) && crowd150 <= (tkChase ? 6 : 5) && now > chaseBan) { activeChaseId = chase.id; chaseStart = now; }
    const activeChase = activeChaseId == null ? null : fleeing.find(e => e.id === activeChaseId);
    if (!activeChase) activeChaseId = null;

    // THỨ TỰ 1: Thoát nguy hiểm tức thì
    let dangerX = 0, dangerY = 0, dangerN = 0, dangerous = false;
    for (const q of ctx.projectiles) {
      const vx = q.vx || 0, vy = q.vy || 0, speed = Math.hypot(vx, vy) || 1, rx = me.x - q.x, ry = me.y - q.y, closing = (rx * vx + ry * vy) / speed;
      // v0.8.2: chỉ né khẩn khi đạn sẽ trúng trong 0.5s; né vuông góc với đường đạn
      const tca = closing / speed, cx = q.x + vx * tca, cy = q.y + vy * tca, miss = Math.hypot(me.x - cx, me.y - cy);
      if (tca > 0 && tca < 0.5 && miss < (q.r || 8) + me.r + 12) {
        let px = -vy / speed, py = vx / speed;
        if ((me.x - cx) * px + (me.y - cy) * py < 0) { px = -px; py = -py; }
        dangerX += px; dangerY += py; dangerN++; dangerous = true;
      }
    }
    for (const h of ctx.hazards) {
      if (!hzPending(h)) continue;
      const hx = Number(h.x ?? h.cx ?? h.centerX), hy = Number(h.y ?? h.cy ?? h.centerY);
      if (!Number.isFinite(hx) || !Number.isFinite(hy)) continue;
      let hd = Math.hypot(me.x - hx, me.y - hy) - (Number(h.r ?? h.radius) || 48);
      if (String(h.kind || h.type || '').toLowerCase().includes('beam')) {
        const len = Number(h.len ?? h.length) || 360, ang = Number(h.angle) || 0, ex = hx + Math.cos(ang) * len, ey = hy + Math.sin(ang) * len, dx = ex - hx, dy = ey - hy, t = clamp(((me.x - hx) * dx + (me.y - hy) * dy) / (dx * dx + dy * dy || 1), 0, 1);
        hd = Math.hypot(me.x - (hx + t * dx), me.y - (hy + t * dy)) - (Number(h.w) || 20) / 2;
      }
      if (hd < me.r + 45 || ctx.hazardInside(me.x, me.y)) { dangerX += me.x - hx; dangerY += me.y - hy; dangerN++; dangerous = true; }
    }
    const riftPt = state.autoRift && !ctx.inArena && ctx.rift ? xyPoint(ctx.rift) : null;
    const riftNear = riftPt && dist(me, riftPt) < 700 && (ctx.rift.ttl == null || Number(ctx.rift.ttl) > 0);
    const holding = String(goalState.key || '').endsWith('#hold') && now - goalState.since < 12000;
    if (state.dodge && dangerous && dangerN && !riftNear && !holding) {
      const m = Math.hypot(dangerX, dangerY) || 1;
      return setGoal({ x: me.x + dangerX / m * 220, y: me.y + dangerY / m * 220, weight: 3, mode: 'né', key: 'danger' }, 'thoát nguy hiểm tức thì');
    }

    // v0.8.2: SUỐI HỒI MÁU (spring): đứng trong ~20px hồi 14% máu/giây
    if (hp < (near150.length <= 1 ? 0.7 : 0.5) || (goalState.mode === 'suối' && hp < 0.95)) {
      const sprs = (ctx.specials || []).filter(sp => sp && sp.type === 'spring' && (sp.charge == null || sp.charge > (goalState.mode === 'suối' ? 0.04 : 0.2)));
      const spr = near150.length >= 8 ? null : sprs.map(sp => ({ sp, pos: xyPoint(sp) })).filter(o => o.pos && dist(me, o.pos) < (near150.length >= 4 ? 300 : 450)).sort((a, b) => dist(me, a.pos) - dist(me, b.pos))[0];
      if (spr) {
        const key = `spring:${spr.sp.id ?? spr.pos.x + ',' + spr.pos.y}`;
        if (!(propBlacklist.has(key) && now < propBlacklist.get(key))) {
          const dS = dist(me, spr.pos);
          if (dS < 18) return setGoal({ x: me.x, y: me.y, weight: 2.6, mode: 'suối', key: key + '#hold', hold: true, center: spr.pos, holdR: 20 }, `đứng hồi máu ở suối (HP ${(hp * 100).toFixed(0)}%)`);
          return setGoal({ x: spr.pos.x, y: spr.pos.y, weight: 2.6, mode: 'suối', key }, `đi tới suối hồi máu, cách ${dS.toFixed(0)}px`);
        }
      }
    }

    // THỨ TỰ 2: Cổng Rift — COMMIT NGAY KHI PHÁT HIỆN RIFT (MIỄN CÒN KỊP TỚI)
    if (ctx.inArena) stickyRift = null;
    const riftObj = ctx.rift;
    const riftPos = xyPoint(riftObj);
    const mySpeed = Math.max(1, me.baseSpd || me.spd || 90);
    const distToRift = riftPos ? dist(me, riftPos) : Infinity;
    const estTimeNeeded = distToRift / mySpeed; // Thời gian ước tính di chuyển tới rift
    
    const riftTimeLeft = (riftObj && riftObj.ttl != null) ? Number(riftObj.ttl) : 999;   // v0.9.13: ttl ĐÃ là thời gian còn lại (game trừ dần) — bản cũ trừ thêm t nên bỏ rift sau ~20s
    const riftValid = riftObj && (riftTimeLeft > estTimeNeeded);

    if (state.autoRift && riftValid && !ctx.inArena && riftPos) {
      stickyRift = { goal: riftPos, at: now };
    } else {
      stickyRift = null;
    }

    const riftGoal = state.autoRift && !ctx.inArena && riftValid ? (stickyRift?.goal || riftPos) : null;

    // THỨ TỰ 3: Sự kiện (Meowth / Giải cứu)
    const rescue = eventObj && (eventObj.target || eventObj.rescue || eventObj.x != null || eventObj.position) ? (eventObj.target || eventObj.rescue || eventObj.position || eventObj) : null;
    const rescueGoal = rescue ? xyPoint(rescue) : null;
    const eventGoal = activeChase && state.events && hp >= .35 ? (() => {
      const d = dist(me, activeChase), speed = Math.max(1, me.baseSpd || me.spd || 90), lead = Math.min(1.2, d / speed);
      return { x: activeChase.x + (activeChase.__vx || 0) * lead, y: activeChase.y + (activeChase.__vy || 0) * lead, key: `meowth:${activeChase.id}:${Math.round(now/100)}` };
    })() : (state.events && rescueGoal ? { ...rescueGoal, key: 'rescue' } : null);

    const relocateCanInterrupt = (hp < .35 || urgentClose) && (near120.length >= 8 || close.length > 0);

    // Xử lý Arena: Boss Articuno
    if (ctx.inArena) {
      const boss = ctx.enemies.filter(e => e.boss).sort((a, b) => dist(me, a) - dist(me, b))[0];
      if (boss) {
        const d = dist(me, boss);
        const dt = (now - lastBossCheckTime) / 1000;
        lastBossCheckTime = now;

        if (lastBossDist !== null && dt > 0) {
          const speedClosing = (lastBossDist - d) / dt;
          const phaseStr = String(boss.phase || boss.state || '').toLowerCase();
          if (speedClosing > 150 || (phaseStr !== 'walk' && phaseStr !== '' && phaseStr !== 'idle')) {
            bossEscapeUntil = now + 600;
            const dirX = me.x - boss.x, dirY = me.y - boss.y, len = Math.hypot(dirX, dirY) || 1;
            bossEscapeVector = [-dirY / len, dirX / len];
          }
        }
        lastBossDist = d;

        if (now < bossEscapeUntil) {
          return setGoal({ x: me.x + bossEscapeVector[0] * 200, y: me.y + bossEscapeVector[1] * 200, weight: 3.5, mode: 'né lao boss', key: 'boss_escape' }, 'né đòn lao của Boss Articuno');
        }

        patrolAngle = (patrolAngle + patrolStep(0.9)) % (Math.PI * 2);
        const radius = clamp(d, 260, 320);
        const targetX = boss.x + Math.cos(patrolAngle) * radius;
        const targetY = boss.y + Math.sin(patrolAngle) * radius;
        return setGoal({ x: targetX, y: targetY, weight: 1.5, mode: 'arena', key: 'arena_orbit' }, 'đánh boss arena, thả diều vòng 260–320px');
      }
    }

    // NẾU CÓ RIFT HỢP LỆ: ĐI THẲNG TỚI RIFT BẰNG COMMIT CHẾ ĐỘ ƯU TIÊN CAO (Trừ khi quái vây quá khẩn cấp)
    if (riftGoal && (!relocateCanInterrupt || dist(me, riftGoal) < 500)) {
      const dRift = dist(me, riftGoal);
      if (dRift < 24 && typeof W.__PL?.Rift?.enterRequest === 'function') {
        safe(() => W.__PL.Rift.enterRequest(), null);
      }
      return setGoal({ ...riftGoal, weight: 2.8, mode: 'rift', key: 'rift', rush: dRift < 350 && hp > 0.4 }, `rift dist=${dRift.toFixed(1)}px (commit${dRift < 350 && hp > 0.4 ? ', lao tới' : ''})`);
    }

    { const sg = !urgentClose && hp > .35 ? specialGoal(ctx, hp) : null;
      if (sg) return setGoal({ x: sg.x, y: sg.y, key: sg.key, weight: 2.4, mode: sg.mode }, sg.reason); }
    { const cg = !urgentClose ? coopGoal(ctx, hp) : null;
      if (cg) { const { reason: cr, ...cgoal } = cg; return setGoal({ ...cgoal, weight: 2.1 }, cr); } }
    if (eventGoal && !relocateCanInterrupt) {
      return setGoal({ ...eventGoal, weight: 2.3, mode: activeChase ? 'đuổi Meowth' : 'sự kiện' }, activeChase ? 'đón đầu Meowth' : 'đi tới sự kiện');
    }

    // v0.9.1: săn hòm toàn map (không xét máu / số quái)
    if ((state.chestHunt || state.chestForce) && state.chest && !ctx.inArena && worldKey === '0') {
      const hg = chestHuntGoal(ctx, now);
      if (hg) return setGoal(hg.goal, hg.reason);
    }

    // v0.8.2: VẬT ĐẶC BIỆT theo mã game: bigchest (đứng gần 3.5s), altar (cột buff), chest (hòm nhỏ đánh vỡ)
    if ((state.chest || state.buff) && hp > .6) {
      const strong = (me.level || 1) >= 6 && hp > 0.45;
      const cands = [];
      const memSp = [...mapMem.values()].filter(m => Math.hypot(m.x - me.x, m.y - me.y) < 650).map(m => m.sp);
      const allSp = [...new Set([...(ctx.specials || []), ...memSp])];
      for (const sp of allSp) {
        if (!sp || sp.dead) continue;
        const pos = xyPoint(sp); if (!pos) continue;
        const key = `sp:${sp.type}:${sp.id ?? (pos.x + ',' + pos.y)}`;
        if (propBlacklist.has(key) && now < propBlacklist.get(key)) continue;
        const dS = dist(me, pos);
        if (sp.type === 'bigchest') {
          // v0.8.2: hòm đã mở xong (thanh mở từng >= 1 rồi tụt về ~0) -> bỏ qua
          const tr = chestTrack.get(key) || { max: 0 };
          const op = Number(sp.open) || 0;
          if (op > tr.max) tr.max = op;
          chestTrack.set(key, tr);
          if (tr.max >= 3.0 && op < 0.2) { propBlacklist.set(key, now + 300000); continue; }
          // xa quá mà gần còn XP thì thôi
          if (dS > 600) continue;
        }
        if (sp.type === 'bigchest' && state.chest && (near150.length <= 2 || (strong && near150.length <= 5)) && dS < 900) cands.push({ sp, pos, key, dS, pri: 3 });
        else if (sp.type === 'altar' && state.buff && !sp.used && near150.length < 6 && dS < 550) cands.push({ sp, pos, key, dS, pri: 2 });
        else if (sp.type === 'chest' && state.chest && near150.length < 5 && dS < 400) cands.push({ sp, pos, key, dS, pri: 1 });
      }
      // đang mở hòm dở thì ưu tiên giữ nguyên hòm đó
      cands.sort((p, q) => (String(goalState.key).startsWith(q.key)) - (String(goalState.key).startsWith(p.key)) || q.pri - p.pri || p.dS - q.dS);
      let c = cands[0];
      // giữ mục tiêu vật đặc biệt đã chọn kể cả khi nó tạm rời danh sách quét
      if (!c && stickySpecial && now < stickySpecial.until && !stickySpecial.sp.used && !stickySpecial.sp.dead && !(propBlacklist.has(stickySpecial.key) && now < propBlacklist.get(stickySpecial.key)) && near150.length < 6) c = { ...stickySpecial, dS: dist(me, stickySpecial.pos) };
      if (c && (!stickySpecial || stickySpecial.key !== c.key)) stickySpecial = { sp: c.sp, pos: c.pos, key: c.key, pri: c.pri, until: now + 12000 };
      if (c) {
        if (c.sp.type === 'bigchest') {
          const zoneR = Math.max(46, me.r + (c.sp.r || 14) + 24) - 2;
          if (c.dS < zoneR) {
            if (near150.length >= 6 || hp < 0.35) { propBlacklist.set(c.key, now + 10000); }
            else if (goalState.key === c.key + '#hold' && now - goalState.since > 4500 && (Number(c.sp.open) || 0) < 0.3) { propBlacklist.set(c.key, now + 60000); }
            else return setGoal({ x: me.x, y: me.y, weight: 2.2, mode: 'mở hòm', key: c.key + '#hold', hold: true, center: c.pos, holdR: zoneR }, `đứng mở hòm to (${(Number(c.sp.open) || 0).toFixed(1)}/3.5s)`);
          } else {
            const dx = me.x - c.pos.x, dy = me.y - c.pos.y, L = Math.hypot(dx, dy) || 1;
            return setGoal({ x: c.pos.x + dx / L * 40, y: c.pos.y + dy / L * 40, weight: 2.2, mode: 'tới hòm', key: c.key, rush: c.dS < 350 && hp > 0.4 }, `đi tới hòm to, cách ${c.dS.toFixed(0)}px`);
          }
        } else if (c.sp.type === 'altar') {
          const dx = me.x - c.pos.x, dy = me.y - c.pos.y, L = Math.hypot(dx, dy) || 1;
          if (c.dS < 36) { propBlacklist.set(c.key, now + 60000); }
          else return setGoal({ x: c.pos.x + dx / L * 26, y: c.pos.y + dy / L * 26, weight: 2.0, mode: 'cột buff', key: c.key }, `đi tới cột buff (altar), cách ${c.dS.toFixed(0)}px`);
        } else {
          const dx = me.x - c.pos.x, dy = me.y - c.pos.y, L = Math.hypot(dx, dy) || 1;
          return setGoal({ x: c.pos.x + dx / L * 40, y: c.pos.y + dy / L * 40, weight: 1.6, mode: 'rương', key: c.key }, `đánh vỡ hòm nhỏ, cách ${c.dS.toFixed(0)}px`);
        }
      }
    }

    // RELOCATE CHỐNG RUNG VÀ PHÁ VÂY: Khi >= 10 quái trong 150px duy trì > 2s -> Chọn điểm xa >= 450px và giữ ít nhất 3s
    if (near150.length >= 10) {
      if (!relocate.denseSince) relocate.denseSince = now;
    } else {
      relocate.denseSince = 0;
    }

    const denseSurrounded = relocate.denseSince && (now - relocate.denseSince >= 2000);
    if (relocate.disarmed && (near120.length >= 8 || close.length === 0)) relocate.disarmed = false;
    const relocating = state.relocate && !relocate.disarmed && (denseSurrounded || near120.length >= 8 || close.length > 0);

    if (relocate.active) {
      if (now < relocate.until) {
        if (relocate.goal && !blocked(ctx, relocate.goal.x, relocate.goal.y)) {
          return setGoal({ ...relocate.goal, weight: 2.5, mode: 'relocate' }, 'giữ điểm relocate xa (ít nhất 3s)');
        }
      } else if (near150.length < 4) {
        relocate.active = false; relocate.goal = null; relocate.disarmed = true; goalState.reason = 'đám quái đã thưa';
      }
    }

    if (relocating && (!eventGoal && !riftGoal || relocateCanInterrupt) && (!relocate.active || !relocate.goal || now >= relocate.until)) {
      relocate.left = relocate.left.filter(z => now - z.t < 5000);
      const pack = near150.length ? near150 : ctx.enemies.filter(e => dist(me, e) < 300);
      const candidates = [];

      for (let i = 0; i < 16; i++) {
        const angle = i * Math.PI * 2 / 16;
        for (const radius of [450, 520, 600]) { // Tìm điểm xa >= 450px
          const cand = { x: me.x + Math.cos(angle) * radius, y: me.y + Math.sin(angle) * radius, mode: 'relocate', key: `relocate:${i}:${radius}` };
          if (blocked(ctx, cand.x, cand.y) || relocate.left.some(z => now - z.t < 5000 && dist(z, cand) < 120)) continue;

          let pressure = 0;
          for (const e of ctx.enemies) {
            const ex = e.x + (e.__vx || 0) * .6, ey = e.y + (e.__vy || 0) * .6;
            const d = Math.hypot(cand.x - ex, cand.y - ey);
            pressure += 10000 / ((d + 30) * (d + 30));
          }
          pressure += scorePoint(ctx, cand.x, cand.y) * .12;
          candidates.push({ cand, pressure });
        }
      }

      let best = null;
      for (const item of candidates.sort((a, b) => a.pressure - b.pressure).slice(0, 10)) {
        const waypoint = astarWaypoint(ctx, item.cand);
        if (pathCache.reachable) { best = item.cand; break; }
      }
      if (best) {
        relocate.active = true; relocate.goal = best; relocate.until = now + 3000; // Giữ ít nhất 3 giây
        relocate.left.push({ x: me.x, y: me.y, t: now });
        return setGoal({ ...best, weight: 2.5 }, 'mật độ quái cao > 2s; relocate xa >= 450px giữ 3s');
      }
    }

    // THỨ TỰ 6: XP
    const earlyGame = (ctx.gameT || 0) < 150;
    const lootCrowd = earlyGame ? 9 : (hp >= .5 ? 7 : 4);
    if (state.loot && near150.length < lootCrowd && goalState.mode === 'loot' && goalState.goal && now - goalState.since < 1500) {
      const target = ctx.pickups.find(p => String(p.id) === String(goalState.pickupId));
      if (target && !(propBlacklist.has(goalState.key) && now < propBlacklist.get(goalState.key))) return setGoal({ ...goalState.goal, weight: 1, mode: 'loot', key: goalState.key, pickupId: goalState.pickupId }, 'giữ cụm XP ít nhất 1.5s');
    }

    // v0.8.2: quái đông vẫn nhặt đồ nằm ở hướng thoáng (ít quái, ít đạn)
    if (state.loot && near150.length >= lootCrowd && hp >= .35) {
      const secOf2 = (x, y) => ((Math.round(Math.atan2(y - me.y, x - me.x) / (Math.PI / 4)) % 8) + 8) % 8;
      const safeItems = ctx.pickups.filter(p => p && dist(me, p) < 220 && dist(me, p) > 18 && sectorThreat[secOf2(p.x, p.y)] < 0.6 && sectorShots[secOf2(p.x, p.y)] < 0.3 && !(propBlacklist.has(`${p.kind}:${p.id ?? p.x + ',' + p.y}`) && now < propBlacklist.get(`${p.kind}:${p.id ?? p.x + ',' + p.y}`)));
      const sp2 = safeItems.sort((a, b) => lootValue(b) / (1 + dist(me, b) / 100) - lootValue(a) / (1 + dist(me, a) / 100))[0];
      if (sp2) return setGoal({ x: sp2.x, y: sp2.y, weight: 1.2, mode: 'loot', key: `${sp2.kind}:${sp2.id ?? sp2.x + ',' + sp2.y}`, pickupId: sp2.id, kind: sp2.kind }, `nhặt ${sp2.kind} ở hướng thoáng`);
    }

    if (state.loot && near150.length < lootCrowd && hp >= .35) {
      const candidates = ctx.pickups.filter(p => p && dist(me, p) > (/xp/i.test(String(p.kind)) ? (me.magnet || 78) : 18));
      let best = null, bscore = -Infinity;
      for (const p of candidates) {
        const goalPt = { x: p.x, y: p.y };
        if (propBlacklist.has(`${p.kind}:${p.id ?? p.x + ',' + p.y}`) && now < propBlacklist.get(`${p.kind}:${p.id ?? p.x + ',' + p.y}`)) continue;
        if (!pointOnSafePath(ctx, goalPt)) continue;
        let value = lootValue(p), chain = 0, from = { x: p.x, y: p.y };
        const others = candidates.filter(q => q !== p).sort((a, b) => dist(from, a) - dist(from, b)).slice(0, 2);
        for (const q of others) chain += lootValue(q) / (1 + dist(from, q) / 100);
        const d = dist(me, p), danger = scorePoint(ctx, p.x, p.y);
        const score = (value + chain * .7) / (1 + d / 180) - danger * .035;
        if (score > bscore) {
          bscore = score;
          best = { x: p.x, y: p.y, weight: 1, mode: 'loot', key: `${p.kind}:${p.id ?? p.x + ',' + p.y}`, pickupId: p.id, kind: p.kind };
        }
      }
      if (best) return setGoal(best, `nhặt ${best.kind || 'đồ'}; điểm ${bscore.toFixed(1)}`);
    }

    // v0.9.1: không còn hòm nào đã biết -> thám hiểm (chỉ khi quanh đây vắng quái)
    if (((state.chestHunt && state.chestExplore) || state.chestForce) && state.chest && !ctx.inArena && worldKey === '0' && huntStats.active === 0 && (state.chestForce || (hp > 0.5 && !me.inLiquid && !ctx.enemies.some(e => dist(me, e) < 260)))) {
      const xg = exploreGoal(ctx, now);
      if (xg) return setGoal(xg, 'chưa biết hòm nào — thám hiểm vùng mới');
    }

    // THỨ TỰ 7: Tuần tra (Patrol Kiting)
    let nearestEnemy = null, nearestD = Infinity;
    for (const e of ctx.enemies) { const d = Math.hypot(e.x - me.x, e.y - me.y); if (d < nearestD) { nearestD = d; nearestEnemy = e; } }
    if (nearestEnemy) {
      patrolAngle = (patrolAngle + patrolStep(0.6)) % (Math.PI * 2);
      const targetX = nearestEnemy.x + Math.cos(patrolAngle) * 195;
      const targetY = nearestEnemy.y + Math.sin(patrolAngle) * 195;
      return setGoal({ x: targetX, y: targetY, weight: 0.8, mode: 'tuần tra', key: `patrol:${nearestEnemy.id}` }, 'kiting quanh quái tự tạo XP');
    } else if (patrolStartPos) {
      patrolAngle = (patrolAngle + patrolStep(0.35)) % (Math.PI * 2);
      let targetX = patrolStartPos.x + Math.cos(patrolAngle) * 300;
      let targetY = patrolStartPos.y + Math.sin(patrolAngle) * 300;
      if (blocked(ctx, targetX, targetY)) {
        patrolAngle += Math.PI / 2;
        targetX = patrolStartPos.x + Math.cos(patrolAngle) * 300;
        targetY = patrolStartPos.y + Math.sin(patrolAngle) * 300;
      }
      return setGoal({ x: targetX, y: targetY, weight: 0.5, mode: 'tuần tra', key: 'patrol_area' }, 'tuần tra diện rộng quanh vị trí đầu');
    }

    return setGoal(null, 'không có mục tiêu ưu tiên');
  }

  const LOOT_VALUE = { magnet: 40, item: 30, ivgem: 30, ticket10: 30, ticket: 20, pumpkinGold: 28, pumpkin: 14, bomb: 12, heal: 10, coin: 7, xpBig: 6 };
  const lootValue = p => {
    if (state.ticketFocus) { if (p.kind === 'ticket10') return 140; if (p.kind === 'ticket') return 80; }
    return LOOT_VALUE[p.kind] ?? (Number(p.value) || 1);
  };
  function xyPoint(o) {
    if (!o) return null;
    const x = Number(o.x ?? o.cx ?? o.worldX ?? (Number.isFinite(o.tx) ? o.tx * TS + 16 : NaN));
    const y = Number(o.y ?? o.cy ?? o.worldY ?? (Number.isFinite(o.ty) ? o.ty * TS + 16 : NaN));
    return Number.isFinite(x) && Number.isFinite(y) ? { x, y } : null;
  }

  function pointSegmentDistance(p, a, b) {
    const dx = b.x - a.x, dy = b.y - a.y;
    const t = clamp(((p.x - a.x) * dx + (p.y - a.y) * dy) / (dx * dx + dy * dy || 1), 0, 1);
    return Math.hypot(p.x - (a.x + t * dx), p.y - (a.y + t * dy));
  }

  function pointRouteDistance(p, route, start) {
    let best = Infinity, prev = start;
    for (const node of [...route].reverse()) {
      best = Math.min(best, pointSegmentDistance(p, prev, node));
      prev = node;
    }
    return best;
  }

  function setGoal(goal, reason) {
    const now = Date.now();
    const newMode = goal?.mode || 'né';

    if (newMode !== lastBotMode && (newMode === 'rift' || lastBotMode === 'rift' || newMode === 'relocate' || lastBotMode === 'relocate')) {
      if (now - lastModeChangeAt < 1200) {
        return goalState.goal ? goalState.goal : goal;
      }
    }
    if (newMode !== lastBotMode) {
      lastModeChangeAt = now;
      lastBotMode = newMode;
    }

    if (!goal) {
      if (currentTarget || targetReason !== reason) {
        targetReasonChangedAt = now;
        console.info(`${TAG} mục tiêu đổi: không có — ${reason}`);
      }
      goalState = { key: '', goal: null, mode: '', since: now, reason };
      currentTarget = ''; targetReason = reason;
      return null;
    }

    const key = goal.key || `${goal.mode}:${Math.round(goal.x / 32)},${Math.round(goal.y / 32)}`;
    if (key !== goalState.key) {
      goalState = { key, goal: { x: goal.x, y: goal.y }, mode: goal.mode, since: now, reason, pickupId: goal.pickupId, startPos: { x: goal.x, y: goal.y }, limMs: goal.limMs, final: goal.final };
      currentTarget = goal.mode; targetReason = reason; targetReasonChangedAt = now;
      console.info(`${TAG} mục tiêu đổi: ${currentTarget} — ${reason}`);
    } else {
      if (goal.final) { goalState.final = goal.final; goalState.goal = { x: goal.x, y: goal.y }; }
      if (reason !== targetReason) { targetReason = reason; goalState.reason = reason; targetReasonChangedAt = now; }
    }
    return goal;
  }

  // ===== v0.8.7: né vùng chủ động + thoát kẹt 1-2s + tiến độ tới mục tiêu =====
  const us = { hist: [], until: 0, vec: [0, 0], level: 0, lastAt: -1e9, lastAng: null, lastMag: 0, gc: { key: '', d: null, at: 0, fails: 0 }, warn: '', warnUntil: 0, enrageLogged: false, nova: null, titanPh: -1, zeroSince: 0, zeroKey: '', zeroN: 0, zeroAt: 0 };
  function unstickPick(ctx, level) {
    const me = ctx.me; let best = [1, 0], bs = -1e9, bang = 0;
    const gAng = goalState.goal ? Math.atan2(goalState.goal.y - me.y, goalState.goal.x - me.x) : null;
    for (let k = 0; k < 24; k++) {
      const a = k * Math.PI / 12, dx = Math.cos(a), dy = Math.sin(a); let run = 0;
      for (let d = 8; d <= 260; d += 8) {
        const x = me.x + dx * d, y = me.y + dy * d;
        if (safe(() => ctx.world.isWall(x, y), false) || (typeof ctx.world.isFree === 'function' && !safe(() => ctx.world.isFree(x, y), true))) break;
        run = d;
      }
      let sc = run + Math.random() * 6;
      if (level === 0 && gAng != null) sc += Math.cos(a - gAng) * 40;
      if (us.lastAng != null && Math.abs(Math.atan2(Math.sin(a - us.lastAng), Math.cos(a - us.lastAng))) < 0.7) sc -= 150;
      if (sc > bs) { bs = sc; best = [dx, dy]; bang = a; }
    }
    us.lastAng = bang; return best;
  }
  let forcedGoal = null;   // v0.9.12: phải khai báo ngoài think() vì think0() cũng đọc (v0.9.11 lỗi ReferenceError ở đây)
  function usWarn(t) { us.warn = t; us.warnUntil = Date.now() + 4000; }
  function think(ctx) {
    if (!ctx) return [0, 0];
    const now = Date.now(), me = ctx.me;
    const playing = state.enabled && W.__PL?.Game?.state === 'playing';
    forcedGoal = null;   // v0.9.12: biến cấp module (think0 dùng chung) — mở hòm bất chấp
    // v0.9.20: tắt "Boss phán xét (phút 30)" mà game đã kéo vào Judgment → đứng im cho tới khi thua (kết thúc ván). Bật thì chơi bình thường.
    if (playing && !state.judgeMode && safe(() => !!W.__PL.Judgment?.active, false)) {
      botMode = 'đứng im (tắt Boss phán xét)'; us.lastMag = 0; us.hist = []; us.until = 0;
      return [0, 0];
    }
    // v0.9.20: ghi nhật ký Titan (đổi pha, NOVA có/không vòng an toàn, bot có đứng trong vòng lúc nổ không)
    try {
      const T = state.titanMode ? ctx.titan : null;
      const bh = T && T.boss && T.boss.maxHp > 0 ? Math.round(100 * T.boss.hp / T.boss.maxHp) : 0, myhp = me && me.maxHp > 0 ? Math.round(100 * me.hp / me.maxHp) : 0;
      if (T && !T.portal) {
        if (T.phase !== us.titanPh) { us.titanPh = T.phase; W.__PLH_RUN_LOG?.recordTitan?.({ e: 'phase', ph: T.phase, bh }); }
        const nv = T.nova;
        if (nv) { if (!us.nova) us.nova = { safe: nv.safe }; us.nova.x = nv.x; us.nova.y = nv.y; us.nova.lx = me.x; us.nova.ly = me.y; }
        else if (us.nova) { const n = us.nova; us.nova = null; W.__PLH_RUN_LOG?.recordTitan?.({ e: 'nova', safe: !!n.safe, inside: !!n.safe && ((n.lx - n.x) ** 2 + ((n.ly - n.y) / 0.75) ** 2 < 22500), hp: myhp }); }
        if (T.enrage && !us.enrageLogged) { us.enrageLogged = true; W.__PLH_RUN_LOG?.recordTitan?.({ e: 'cuồng nộ (quá 360s)', ph: T.phase, bh, hp: myhp }); }
      } else { us.titanPh = -1; us.nova = null; us.enrageLogged = false; }
    } catch (_) {}
    // v0.9.20: Titan cuồng nộ (quá 360s): không còn vòng an toàn, không đủ điều kiện hạ → lao vào Titan để bị hạ gục. KHÔNG dùng hàm rời của game (sợ tính là bỏ cả ván).
    if (playing && state.titanMode && ctx.titan && !ctx.titan.portal && ctx.titan.enrage) {
      const T = ctx.titan, bx = T.boss ? T.boss.x : T.cx, by = T.boss ? T.boss.y : T.cy, dx = bx - me.x, dy = by - me.y, dd = Math.hypot(dx, dy);
      botMode = 'tự thua (Titan cuồng nộ)'; us.lastMag = 1; us.hist = []; us.until = 0;
      return Number.isFinite(dd) && dd > 6 ? [dx / dd, dy / dd] : [0, 0];
    }
    if (playing) {
      try {
        if (state.judgeMode && !ctx.coop?.active) {
          const gt = safe(() => Number(W.__PL.Game.st.time) || 0, 0), pl = W.__PL.Game.player;
          if (gt > 1500 && gt < 1800 && pl && (pl.level < 30 || (pl.kills || 0) < 54) && now > us.warnUntil) usWarn('Solo cần cấp 30 và 54 quái trước 30:00 để Arceus xuất hiện');
        }
        // v0.9.13: RIFT LÀ VIỆC ƯU TIÊN SỐ 1 — còn kịp tới là lao thẳng vào, bất chấp quái / đạn / vùng nguy hiểm / nước / máu / hòm
        {
          const wasRush = riftRush; riftRush = false;
          if (state.autoRift && !ctx.inArena && ctx.rift) {
            const rp = xyPoint(ctx.rift);
            if (rp) {
              const d = dist(me, rp), spd = Math.max(1, me.baseSpd || me.spd || 90), left = ctx.rift.ttl != null ? Number(ctx.rift.ttl) : 999;
              if (left > d / spd * (wasRush ? 0.5 : 0.85) && left > 0.8) {   // đã lao rồi thì kiên trì hơn (không bỏ giữa chừng khi bị quái cản)
                riftRush = true;
                if (d < 24 && typeof W.__PL?.Rift?.enterRequest === 'function') safe(() => W.__PL.Rift.enterRequest(), null);
                const rg = { x: rp.x, y: rp.y, weight: 3, mode: 'rift', key: 'rift', rush: d < 350, force: true };
                setGoal(rg, `RIFT ưu tiên số 1 — cách ${Math.round(d)}px, còn ${left > 900 ? '?' : Math.round(left)}s`);
                forcedGoal = rg;
              }
            }
          }
          // v0.9.20: CỔNG TITAN — xuất hiện là lao vào ngay, ưu tiên trên mọi thứ (không điều kiện máu / thời gian / khoảng cách / quái)
          if (!ctx.inArena && ctx.titan && ctx.titan.portal && Number.isFinite(ctx.titan.portal.x)) {
            const tp = ctx.titan.portal, td = dist(me, tp);
            riftRush = true;
            const tg = { x: tp.x, y: tp.y, weight: 3, mode: 'cổng Titan', key: 'titan:portal', rush: td < 350, force: true };
            setGoal(tg, `CỔNG TITAN ưu tiên số 1 — cách ${Math.round(td)}px`);
            forcedGoal = tg;
          }
          if (riftRush !== wasRush) { blkAt = 0; wetCacheT = 0; }
          ctx.riftRush = riftRush;
        }
        // v0.9.13: vừa xong rift (ra khỏi arena) → mở lại các hòm đang bị cấm tạm / bỏ dở (trừ hòm đã mở xong)
        if (ctx.inArena) us.wasArena = true;
        else if (us.wasArena) { us.wasArena = false; for (const k of [...propBlacklist.keys()]) if (String(k).startsWith('sp:') && !chestTrack.get(k)?.counted) propBlacklist.delete(k); huntFails.clear(); }
        // v0.9.11: MỞ HÒM BẤT CHẤP — có hòm (hoặc đang tìm hòm) thì đi thẳng tới mở, bỏ qua né quái / né đòn / né vùng, bất kể máu (v0.9.13: nhường cho rift)
        if (!forcedGoal && state.chestForce && state.chest && !ctx.inArena && worldKey === '0') {
          const hg = chestHuntGoal(ctx, now);
          if (hg) { const cg = { ...hg.goal, force: true }; setGoal(cg, 'mở hòm bất chấp — ' + hg.reason); forcedGoal = cg; }
          else if (huntStats.active === 0) { const xg = exploreGoal(ctx, now); if (xg) { const cg = { ...xg, force: true }; setGoal(cg, 'mở hòm bất chấp — đi tìm hòm'); forcedGoal = cg; } }
        }
        ctx.force = !!forcedGoal;
        const nv = forcedGoal ? null : titanNova(ctx);
        if (nv) { botMode = nv.mode; us.lastMag = Math.hypot(nv.v[0], nv.v[1]); us.gc.key = ''; return nv.v; }
        const hz = forcedGoal ? null : hazardEscape(ctx);
        if (!hz && !forcedGoal) {
          const fl = judgeFlee(ctx);
          if (fl) { botMode = 'né Arceus'; us.lastMag = 1; us.gc.key = ''; return fl; }
        }
        if (hz) { botMode = 'né vùng'; us.lastMag = 1; us.gc.key = ''; return hz; }
        if (now < us.until) { botMode = 'thoát kẹt'; us.lastMag = 1; us.gc.key = ''; return us.vec; }
        // v0.9.20: đang đi tới hòm mà bot tự đứng yên (hướng đi 0) → bộ phát hiện kẹt bên dưới không bắt được (nó chỉ tính khi bot đang cố đi). Sau 1.5s: đổi hướng; lần 2 cùng hòm trong 10s: bỏ hòm đó, chọn hòm khác.
        {
          const gm0 = goalState.mode, gk0 = String(goalState.key || '').split('#')[0];
          if ((gm0 === 'tới hòm' || gm0 === 'rương') && goalState.goal && us.lastMag < 0.05) {
            if (!us.zeroSince) us.zeroSince = now;
            else if (now - us.zeroSince > 1500) {
              us.zeroSince = 0;
              us.zeroN = us.zeroKey === gk0 && now - us.zeroAt < 10000 ? us.zeroN + 1 : 1; us.zeroKey = gk0; us.zeroAt = now;
              W.__PLH_RUN_LOG?.recordChestEv?.('tự đứng yên giữa đường tới hòm');
              if (us.zeroN >= 2) {
                huntFail(me, gk0, now); W.__PLH_RUN_LOG?.recordChestEv?.('bỏ hòm vì tự đứng yên');
                goalState = { key: '', goal: null, mode: '', since: now, reason: 'tự đứng yên → đổi hòm' }; us.gc = { key: '', d: null, at: now, fails: 0 };
              } else { us.vec = unstickPick(ctx, 0); us.until = now + 800; usWarn('đứng yên giữa đường tới hòm → đổi hướng'); botMode = 'thoát kẹt'; us.lastMag = 1; return us.vec; }
            }
          } else us.zeroSince = 0;
        }
        us.hist.push({ t: now, x: me.x, y: me.y, m: us.lastMag });
        while (us.hist.length && now - us.hist[0].t > 2300) us.hist.shift();
        const holding = String(goalState.key || '').endsWith('#hold') || botMode === 'đứng chờ';
        if (!holding) {
          const win = ms => us.hist.filter(h => now - h.t <= ms);
          const chk = (ms, maxMove) => {
            const w = win(ms); if (w.length < 8 || now - w[0].t < ms - 150) return null;
            const act = w.filter(h => h.m > 0.3).length / w.length; if (act < 0.7) return null;
            const mv = Math.max(...w.map(h => Math.hypot(h.x - me.x, h.y - me.y))); return mv < maxMove ? mv : null;
          };
          const mv = chk(1300, 14) ?? chk(2100, 45);
          if (mv != null) {
            const lvl = now - us.lastAt < 7000 ? Math.min(us.level + 1, 2) : 0;
            if (lvl === 0) us.lastAng = null;
            us.level = lvl; us.lastAt = now; us.vec = unstickPick(ctx, lvl); us.until = now + [900, 1400, 2000][lvl];
            const gk = goalState.key; if (gk) { if (goalState.mode === 'tới hòm' || goalState.mode === 'rương') huntFail(me, gk, now); else if (isCoopMode(goalState.mode)) { markBad(me.x, me.y, now); coarse.at = 0; propBlacklist.set(String(gk).split('#')[0], now + 4000); } else propBlacklist.set(gk, now + 20000); }
            goalState = { key: '', goal: null, mode: '', since: now, reason: 'thoát kẹt' };
            us.hist = []; usWarn(`kẹt ${mv.toFixed(0)}px → thoát kẹt (mức ${lvl + 1})`);
            if (W.__PLH_RUN_LOG?.recordUnstick) W.__PLH_RUN_LOG.recordUnstick({ level: lvl + 1, moved: +mv.toFixed(1), x: Math.round(me.x), y: Math.round(me.y), goal: gk || '' });
            console.warn(`${TAG} Thoát kẹt mức ${lvl + 1}: di chuyển ${mv.toFixed(1)}px`);
            botMode = 'thoát kẹt'; us.lastMag = 1; return us.vec;
          }
          // tiến độ tới rương / cột buff
          const gm = goalState.mode;
          if (goalState.goal && (gm === 'rương' || gm === 'cột buff' || gm === 'tới hòm' || isCoopMode(gm)) && !(gm === 'tới hòm' && pathCache.partial)) {
            const key = String(goalState.key).split('#')[0], fin = goalState.final || goalState.goal, d = (gm === 'tới hòm' || gm === 'rương' || isCoopMode(gm)) ? (routeRemain(me, key, fin) ?? dist(me, fin)) : dist(me, fin);
            if (us.gc.key !== key) us.gc = { key, d, at: now, fails: 0 };
            else if (now - us.gc.at >= 2000) {
              if (d > 60 && us.gc.d - d < 12 && us.lastMag > 0.3) {
                us.gc.fails++;
                if (us.gc.fails >= 3) {
                  if (gm === 'tới hòm' || gm === 'rương') huntFail(me, key, now); else if (isCoopMode(gm)) { markBad(me.x, me.y, now); coarse.at = 0; propBlacklist.set(key, now + 8000); } else propBlacklist.set(key, now + 20000);
                  usWarn(`không lại gần được ${gm} → bỏ mục tiêu`);
                  if (W.__PLH_RUN_LOG?.recordUnstick) W.__PLH_RUN_LOG.recordUnstick({ level: 0, moved: 0, x: Math.round(me.x), y: Math.round(me.y), goal: key, reason: 'không lại gần được ' + gm });
                  goalState = { key: '', goal: null, mode: '', since: now, reason: 'bỏ mục tiêu không tới được' }; us.gc = { key: '', d: null, at: now, fails: 0 };
                } else { us.vec = unstickPick(ctx, 1); us.until = now + 700; usWarn(`chưa lại gần ${gm} (${us.gc.fails}/3) → đổi hướng`); us.gc.at = now; us.gc.d = d; }
              } else { us.gc.fails = 0; us.gc.at = now; us.gc.d = d; }
            }
          }
        }
      } catch (e) { console.warn(`${TAG} lỗi thoát kẹt`, e); }
    } else us.hist = [];
    try {
      if (ctx.coop?.active && W.__PLH_RUN_LOG?.recordCoop) {
        W.__PLH_RUN_LOG.recordCoop(ctx.coop.mates.length, !!ctx.coop.isHost);
        const key = String(goalState.key || '');
        if (key !== us.coopKey) { us.coopKey = key; if (key.startsWith('coop:revive')) W.__PLH_RUN_LOG.recordCoopGoal('reviveGoals'); else if (key.startsWith('coop:follow')) W.__PLH_RUN_LOG.recordCoopGoal('followGoals'); }
      }
    } catch (_) {}
    const v = think0(ctx);
    us.lastMag = Math.hypot(v?.[0] || 0, v?.[1] || 0);
    return v;
  }

  function think0(ctx) {
    if (!ctx) return [0, 0];
    try {
      const now = Date.now();
      const me = ctx.me;

      if (false && state.enabled && W.__PL?.Game?.state === 'playing' && !String(goalState.key || '').endsWith('#hold')) {
        if (watchdog.lastX == null) {
          watchdog.lastX = me.x; watchdog.lastY = me.y; watchdog.lastCheckAt = now;
        } else if (now - watchdog.lastCheckAt >= 1500) {
          const moved = Math.hypot(me.x - watchdog.lastX, me.y - watchdog.lastY);
          if (moved < 4) {
            console.warn(`${TAG} Watchdog kích hoạt: nhân vật bị kẹt đứng yên (${moved.toFixed(1)}px/1.5s). Reset mục tiêu.`);
            if (goalState.key) propBlacklist.set(goalState.key, now + 20000);
            goalState = { key: '', goal: null, mode: '', since: now, reason: 'watchdog gỡ kẹt' };
            watchdog.escapeUntil = now + 500;
            watchdog.escapeVector = [Math.random() > 0.5 ? 1 : -1, Math.random() > 0.5 ? 1 : -1];
            if (W.__PLH_RUN_LOG) W.__PLH_RUN_LOG.recordStuck(moved);
          }
          watchdog.lastX = me.x; watchdog.lastY = me.y; watchdog.lastCheckAt = now;
        }
      }

      if (now < watchdog.escapeUntil) return watchdog.escapeVector;

      // v0.8.2: đang đứng trong nước -> ra khỏi nước theo hướng gần bờ nhất (trừ khi đang lao tới rift)
      if (me.inLiquid && !ctx.riftRush && !(goalState.mode === 'rift' && goalState.goal && dist(me, goalState.goal) < 120)) {
        let bestW = null, bestD = 1e9;
        for (let k = 0; k < 16; k++) {
          const a = k * Math.PI / 8, dx = Math.cos(a), dy = Math.sin(a);
          for (let r = 24; r <= 192; r += 24) {
            const x = me.x + dx * r, y = me.y + dy * r;
            if (safe(() => ctx.world.isWall(x, y), false)) break;
            if (!wetAt(ctx, x, y, me.r || 12)) {
              const danger = ctx.enemies.filter(e => Math.hypot(e.x - x, e.y - y) < 40).length * 60;
              if (r + danger < bestD) { bestD = r + danger; bestW = [dx, dy]; }
              break;
            }
          }
        }
        if (bestW) { botMode = 'ra khỏi nước'; return bestW; }
      }

      if (goalState.goal && (goalState.mode === 'rương' || goalState.mode === 'cột buff' || goalState.mode === 'tới hòm' || goalState.mode === 'mở hòm' || isCoopMode(goalState.mode))) {
        const elapsed = now - goalState.since;
        const lim = goalState.limMs || (goalState.mode === 'mở hòm' ? 9000 : goalState.mode === 'tới hòm' ? 12000 : 10000);
        if (elapsed > lim) {
          console.warn(`${TAG} Timeout/kẹt khi tiếp cận ${goalState.mode}. Đưa vào blacklist 20s.`);
          if (goalState.mode === 'tới hòm' || goalState.mode === 'rương') huntFail(me, goalState.key, now); else propBlacklist.set(String(goalState.key).split('#')[0], now + (isCoopMode(goalState.mode) ? 8000 : 20000));
          goalState = { key: '', goal: null, mode: '', since: now, reason: 'timeout rương/buff' };
        }
      }

      // v0.8.2: THOÁT VÂY khi bị quái đè sát và gần như không di chuyển được
      pinHist.push({ t: now, x: me.x, y: me.y });
      pinHist = pinHist.filter(h => now - h.t <= 700);
      const touching = ctx.enemies.filter(e => dist(me, e) < (e.r || 10) + me.r + 16);
      const moved = pinHist.length > 2 ? dist(pinHist[0], me) : 99;
      if (touching.length && moved < 10 && now - pinHist[0].t > 500 && !String(goalState.key || '').endsWith('#hold')) {
        const near = ctx.enemies.filter(e => dist(me, e) < 160);
        let bestDir = null, bestGap = -1;
        for (let k = 0; k < 16; k++) {
          const a = k * Math.PI / 8, dx = Math.cos(a), dy = Math.sin(a);
          if (blocked(ctx, me.x + dx * 40, me.y + dy * 40)) continue;
          let gap = 200;
          for (const e of near) {
            const rx = e.x - me.x, ry = e.y - me.y, along = rx * dx + ry * dy;
            if (along <= -10) continue;
            const lat = Math.abs(rx * dy - ry * dx);
            if (lat < (e.r || 10) + me.r + 6) gap = Math.min(gap, Math.max(0, along));
          }
          const rg = goalState.goal && /rift|hòm/.test(goalState.mode || '') ? goalState.goal : null;
          if (rg) { const gl = Math.hypot(rg.x - me.x, rg.y - me.y) || 1; gap += 80 * Math.max(0, (dx * (rg.x - me.x) + dy * (rg.y - me.y)) / gl); }
          if (gap > bestGap) { bestGap = gap; bestDir = [dx, dy]; }
        }
        if (bestDir) {
          watchdog.escapeUntil = now + 800; watchdog.escapeVector = bestDir; pinHist = [];
          botMode = 'thoát vây';
          return bestDir;
        }
      }

      const goal = forcedGoal || chooseGoal(ctx);
      // v0.8.2: học từ trận tay: khi an toàn và đang tuần tra thì đứng chờ quái tới (tối đa 2.5s, nghỉ 2s)
      if (goal && goal.mode === 'tuần tra' && !ctx.inArena && !me.inLiquid) {
        const nearE = ctx.enemies.reduce((m, e) => Math.min(m, Math.hypot(e.x - me.x, e.y - me.y) - (e.r || 10)), Infinity);
        const nearS = ctx.projectiles.reduce((m, q) => Math.min(m, Math.hypot(q.x - me.x, q.y - me.y)), Infinity);
        const hpOk = (me.hp || 0) / Math.max(1, me.maxHp || 1) > 0.5;
        if (hpOk && nearE > 200 && nearS > 260 && ctx.enemies.length > 0 && now > waitState.cooldownUntil) {
          if (!waitState.since) waitState.since = now;
          if (now - waitState.since < 2500) { botMode = 'đứng chờ'; watchdog.lastX = me.x; watchdog.lastY = me.y; watchdog.lastCheckAt = now; return [0, 0]; }
          waitState.since = 0; waitState.cooldownUntil = now + 2000;
        } else if (waitState.since) { waitState.since = 0; waitState.cooldownUntil = now + 2000; }
      } else waitState.since = 0;
      ctx.rushScale = goal && goal.rush ? 0.25 : 1;
      if (goal && goal.rush) botMode = goal.mode + ' (lao tới)';
      // v0.8.2: bỏ qua món đồ không nhặt được (táo khi đầy máu, sau nước/tường...)
      if (goal && goal.mode === 'loot') {
        const gd = dist(me, goal);
        if (lootTrack.key !== goal.key) lootTrack = { key: goal.key, t0: now, d0: gd, nearSince: 0 };
        else {
          if (gd < 24) { if (!lootTrack.nearSince) lootTrack.nearSince = now; if (now - lootTrack.nearSince > 1000) { propBlacklist.set(goal.key, now + 20000); lootTrack.key = ''; } }
          else lootTrack.nearSince = 0;
          if (now - lootTrack.t0 > 3000) { if (gd > lootTrack.d0 - 30) { propBlacklist.set(goal.key, now + 20000); lootTrack.key = ''; } else { lootTrack.t0 = now; lootTrack.d0 = gd; } }
        }
      }
      let waypoint = goal ? astarWaypoint(ctx, goal) : null;
      // v0.8.2: nhìn xa hơn trên đường A* (waypoint kề bên làm bot thà đứng yên còn hơn đi quá đà)
      let aim = waypoint;
      if (goal && waypoint && (pathCache.reachable || pathCache.partial) && pathCache.route && pathCache.route.length) {
        for (const node of pathCache.route) { if (dist(me, node) <= 150) { aim = node; break; } }
      }
      if (goal && aim && dist(me, goal) < 150 && pathCache.reachable) aim = goal;

      // TRONG MODE COMMIT RIFT: Chỉ né đòn nếu sẽ trúng trong 0.35s, né vuông góc nhưng duy trì tiến về Rift (thành phần hướng tới rift >= 0.5)
      if (goal?.mode === 'rift') {
        let commitDanger = false;
        for (const q of ctx.projectiles) {
          const speed = Math.hypot(q.vx || 0, q.vy || 0);
          const tHit = speed ? dist(me, q) / speed : 999;
          if (tHit <= 0.35) commitDanger = true;
        }
        for (const h of ctx.hazards) {
          if (ctx.hazardInside(me.x, me.y)) commitDanger = true;
        }

        const ax = (aim || waypoint || goal).x - me.x, ay = (aim || waypoint || goal).y - me.y, al = Math.hypot(ax, ay) || 1;
        const wallAhead = blocked(ctx, me.x + ax / al * 36, me.y + ay / al * 36);
        if (ctx.riftRush) commitDanger = false;   // v0.9.13: lao thẳng, bất chấp quái / đạn
        if (!commitDanger && (waypoint || ctx.riftRush) && !wallAhead) {
          const dx = ax, dy = ay, len = al;
          botMode = 'rift (commit)';
          return [dx / len, dy / len];
        }
      }

      const angles = Array.from({ length: 24 }, (_, i) => i * Math.PI * 2 / 24);
      angles.push(null);

      let best = [0, 0], bestScore = Infinity;
      const lp = learnPolicy(ctx);
      const STEPS = (ctx.nearE ? ctx.nearE.length : 0) > 40 ? 8 : 12, STRIDE = 12 / STEPS;   // v0.9.2: quái đông thì tính ít điểm hơn (tầm nhìn vẫn như cũ)

      for (const a of angles) {
        const dx = a === null ? 0 : Math.cos(a), dy = a === null ? 0 : Math.sin(a);
        let score = 0;

        for (let step = 1; step <= STEPS; step++) {
          const sv = step * STRIDE, t = sv / 5, x = ctx.me.x + dx * t * 45, y = ctx.me.y + dy * t * 45;
          score += scorePoint(ctx, x, y, Math.min(1.2, (t * 45) / Math.max(60, ctx.me.baseSpd || ctx.me.spd || 95))) * (1 + sv / 24);
          if (goal && aim) score += Math.hypot(aim.x - x, aim.y - y) * (goal.weight / 30);
        }

        // Đảm bảo trong mode rift commit khi né vẫn tiến về phía rift (thành phần hướng >= 0.5)
        if (goal?.mode === 'rift' && waypoint) {
          const toRiftX = waypoint.x - me.x, toRiftY = waypoint.y - me.y, rLen = Math.hypot(toRiftX, toRiftY) || 1;
          const dotRift = dx * (toRiftX / rLen) + dy * (toRiftY / rLen);
          if (dotRift < 0.5) score += 8000;
        }

        if (goal?.mode === 'relocate' && state.loot && waypoint) {
          for (const pickup of ctx.pickups) {
            if (!pointOnSafePath(ctx, pickup)) continue;
            const along = pointRouteDistance(pickup, pathCache.route, ctx.me);
            if (along <= 60) score -= 140 * lootValue(pickup) / (1 + along / 60);
          }
        }

        if (state.dodge && !ctx.force) {
          const fast = ctx.enemies.filter(e => (e.spd || 0) > (ctx.me.baseSpd || ctx.me.spd || 90) && Math.hypot(e.x - ctx.me.x, e.y - ctx.me.y) < 50);
          for (const e of fast) {
            const rx = ctx.me.x - e.x, ry = ctx.me.y - e.y, d = Math.hypot(rx, ry) || 1;
            score += Math.abs(dx * rx / d + dy * ry / d) * 2200;
          }

          if (ctx.inArena) {
            for (const tHaz of [.2, .4, .6, .8]) {
              const travel = (ctx.me.baseSpd || ctx.me.spd || 90) * tHaz, hx = ctx.me.x + dx * travel, hy = ctx.me.y + dy * travel;
              if (ctx.hazardInside(hx, hy) || ctx.hazardInside(hx + ctx.me.r, hy) || ctx.hazardInside(hx - ctx.me.r, hy) || ctx.hazardInside(hx, hy + ctx.me.r) || ctx.hazardInside(hx, hy - ctx.me.r)) {
                score += 25000;
              }
            }
          }

          for (const q of ctx.projectiles) {
            const speed = Math.hypot(q.vx || 0, q.vy || 0);
            if (speed < 1) continue;
            const perpX = -(q.vy / speed), perpY = q.vx / speed;
            const dot = dx * perpX + dy * perpY;
            if (ctx.inArena) score -= Math.abs(dot) * 120;
            for (let t = .1; t <= 1.2; t += .1) {
              const qx = q.x + q.vx * t, qy = q.y + q.vy * t, px = ctx.me.x + dx * 90 * t, py = ctx.me.y + dy * 90 * t;
              if (Math.hypot(qx - px, qy - py) < (q.r || 8) + ctx.me.r + 14) score += ctx.inArena ? 3000 : 1000;
            }
          }
        }

        if (a !== null) {
          const sec = ((Math.round(a / (Math.PI / 4)) % 8) + 8) % 8;
          score += sectorThreat[sec] * 60 + sectorShots[sec] * 120 - (goal && goal.mode === 'tuần tra' ? sectorLoot[sec] * 40 : 0);
        }
        if (lp.prob && !(goal && goal.hold)) {
          const li = a === null ? 8 : ((Math.round(a / (Math.PI / 4)) % 8) + 8) % 8;
          score -= lp.prob[li] * lp.conf * 1500 * (state.learnMix ?? 0.5) * (goal && goal.rush ? 0.3 : 1);
        }
        if (goal && goal.hold && goal.center) {
          for (let k = 3; k <= 12; k += 3) {
            const px = ctx.me.x + dx * (k / 5) * 45, py = ctx.me.y + dy * (k / 5) * 45;
            if (Math.hypot(px - goal.center.x, py - goal.center.y) > (goal.holdR || 40)) score += 2500;
          }
        } else if (a === null && goal) score += 260 * (goal.weight || 1);
        if (score < bestScore) { bestScore = score; best = [dx, dy]; }
      }

      const mag = Math.hypot(best[0], best[1]);
      botMode = goal?.mode || (ctx.inArena ? 'arena' : 'né');
      const res = mag > 0 ? [best[0] / mag, best[1] / mag] : [0, 0];

      if (!Number.isFinite(res[0]) || !Number.isFinite(res[1])) return [0, 0];
      return res;

    } catch (e) {
      const errStr = String(e?.message || e);
      if (!loggedErrors.has(errStr)) {
        loggedErrors.add(errStr);
        console.error('[PLH] think error:', e);
      }
      setBootStatus('Lỗi tính hướng: ' + errStr, true);

      if (ctx?.me && ctx?.enemies?.length) {
        let closest = ctx.enemies[0]; for (const e of ctx.enemies) if (dist(ctx.me, e) < dist(ctx.me, closest)) closest = e;
        const dx = ctx.me.x - closest.x, dy = ctx.me.y - closest.y, len = Math.hypot(dx, dy) || 1;
        return [dx / len, dy / len];
      }
      return [0, 0];
    }
  }

  // CHẤM ĐIỂM THẺ (CARD SCORING ENGINE V0.8.2)
  // v0.8.2: chiêu tự gây sát thương (recoil) và chiêu không gây sát thương bị hạ điểm
  const RECOIL_MOVES = ['flare-blitz', 'double-edge', 'take-down', 'brave-bird', 'wood-hammer', 'head-smash', 'volt-tackle', 'wild-charge', 'submission', 'high-jump-kick', 'jump-kick', 'struggle', 'head-charge', 'light-of-ruin', 'wave-crash', 'chloroblast', 'mind-blown', 'steel-beam', 'explosion', 'self-destruct', 'memento', 'final-gambit', 'belly-drum', 'curse'];
  const RECOIL_RE = /recoil|retroceso|da[ñn]a (al usuario|a ti)|hurts (you|the user)|costs? (you )?hp|own hp|tu propia vida|te quita vida|self-?damage/i;
  const NODMG_RE = /no hace da[ñn]o|deals no damage|no damage|non fa danni|ne fait pas de d/i;
  function moveIdOf(option) { return String(option.key || '').split(':')[1] || ''; }
  // ===== v0.9.11: chọn thẻ theo danh sách tick (chiêu thức của từng Pokémon + thẻ chỉ số) =====
  const STAT_ORDER = ['hp', 'atk', 'xp', 'mag', 'def', 'rgn', 'cd', 'spd', 'heal'];
  const STAT_LABEL = { hp: 'Máu tối đa (Vigor)', atk: 'Sát thương (Power)', xp: 'Kinh nghiệm (Learning)', mag: 'Nam châm nhặt XP (Magnet)', def: 'Giáp / giảm sát thương (Armor)', rgn: 'Hồi máu mỗi giây (Synthesis)', cd: 'Giảm hồi chiêu (Reflexes)', spd: 'Tốc độ chạy (Sprint)', heal: 'Hồi máu ngay (Sitrus Berry)' };
  let monCache = null;
  const allMons = () => { const P = W.__PL, n = safe(() => P.DEX.length, 0); if (monCache && monCache.n === n && n) return monCache.list; const list = [...(safe(() => P.DEX, []) || []), ...(safe(() => P.DEX_EXTRA, []) || [])].filter(m => m && m.dex != null); monCache = { n, list }; return list; };
  const monByNum = n => allMons().find(m => Number(m.dex) === Number(n)) || null;
  let lastMonDex = Number(safe(() => localStorage.getItem('plh_lastmon'), 0)) || 0;
  const currentMon = () => { const m = safe(() => W.__PL.Game.player.mon, null); if (m && m.dex != null) { if (m.dex !== lastMonDex) { lastMonDex = m.dex; try { localStorage.setItem('plh_lastmon', String(m.dex)); } catch (_) {} } return m; } return lastMonDex ? monByNum(lastMonDex) : null; };
  const movesOfMon = mon => {
    const M = safe(() => W.__PL.Moves, null); if (!mon || !M || !M.BY_ID) return [];
    const ids = []; const add = id => { id = typeof id === 'string' ? id : id && id.id; if (id && M.BY_ID[id] && !ids.includes(id)) ids.push(id); };
    safe(() => add(M.startFor(mon)), null); safe(() => (M.ownFor(mon) || []).forEach(add), null); safe(() => (M.poolFor(mon) || []).forEach(add), null);
    return ids;
  };
  // v0.9.12: chiêu đặc biệt của từng Pokémon (độc quyền / signature / Mega / Shiny / Mega-Shiny) — trước đây không có trong danh sách
  const SPECIAL_KINDS = [['sigFor', '★ Signature'], ['shinyFor', '✦ Shiny (thẻ khi chơi bản Shiny)'], ['uniqFor', '★ Độc quyền (kích hoạt riêng, không có thẻ)'], ['megaFor', '★ Mega (kích hoạt riêng, không có thẻ)'], ['megaShinyFor', '✦ Mega Shiny (kích hoạt riêng, không có thẻ)']];
  const specialsOfMon = mon => {
    const M = safe(() => W.__PL.Moves, null); if (!mon || !M || !M.BY_ID) return [];
    const out = [], seen = new Set(movesOfMon(mon));
    for (const [fn, label] of SPECIAL_KINDS) {
      const v = safe(() => M[fn](mon), null); const arr = Array.isArray(v) ? v : (v && typeof v === 'object' ? [v.start, v.shiny] : (v ? [v] : []));   // sigFor trả {start, shiny}
      for (let id of arr) { id = typeof id === 'string' ? id : id && id.id; if (id && M.BY_ID[id] && !seen.has(id)) { seen.add(id); out.push({ id, label }); } }
    }
    return out;
  };
  const allMovesOfMon = mon => [...movesOfMon(mon), ...specialsOfMon(mon).map(x => x.id)];
  const cardWantMoves = () => { const m = currentMon(); return (m && Array.isArray(state.cardMoves[m.dex]) ? state.cardMoves[m.dex] : []); };
  const cardHasPrefs = () => state.cardStats.length > 0 || cardWantMoves().length > 0;
  function cardPrefBoost(option) {
    if (!state.cardPick || !option) return 0;
    const type = String(option.type || ''), key = String(option.key || '');
    if (type === 'stat') { const sid = key.replace('stat:', ''); return state.cardStats.includes(sid) ? 3000 - Math.max(0, STAT_ORDER.indexOf(sid)) * 10 : 0; }
    if (type === 'new' || type === 'up' || type === 'evo') {
      const id = moveIdOf(option), want = cardWantMoves(), i = want.indexOf(id);
      if (i >= 0) return 3000 + (type === 'evo' ? 150 : type === 'new' ? 60 : 0) - i * 10;
    }
    return 0;
  }
  function scoreCard(option, index) { return scoreCardBase(option, index) + learnCardBonus(option) + cardPrefBoost(option); }
  function scoreCardBase(option, index) {
    if (!option) return 0;
    const type = String(option.type || ''), key = String(option.key || ''), tag = String(option.tag || ''), desc = String(option.desc || '');
    const p = W.__PL?.Game?.player || {};
    const slots = (p.slots || p.moves || []).length, maxMoves = p.maxMoves || 4;
    const hpPct = (p.hp || 0) / Math.max(1, p.maxHp || 1);
    const id = moveIdOf(option);
    const recoil = RECOIL_MOVES.includes(id) || RECOIL_RE.test(desc);
    const noDmg = NODMG_RE.test(desc);
    if (type === 'evo') return 1000 - index * 0.1;
    if (type === 'stat' && /^Evoluciona|^Evolves/i.test(tag)) { const sid0 = key.replace('stat:', ''); return (key === 'stat:cd' ? 380 : 700) - index * 0.1; }
    if (type === 'stat' && key === 'stat:heal') return (hpPct < 0.3 ? 950 : hpPct < 0.5 ? 500 : 20) - index * 0.1;
    // v0.8.2: phân biệt chiêu gây sát thương và chiêu hỗ trợ/bị động
    const SUPPORT_RE = /^Passive:|no hace da|deals no damage|no damage|lower accuracy|it affects them/i;
    const isDmgMove = m => m && !/buff|passive|aura-buff/i.test(String(m.kind || '')) && !SUPPORT_RE.test(String(m.desc || m.def?.desc || ''));
    const pmoves = p.moves || p.slots || [];
    const dmgMoves = pmoves.filter(isDmgMove).length;
    if (type === 'new') {
      if (slots >= maxMoves) return 0;
      if (recoil) return 120 - index * 0.1;
      const support = noDmg || SUPPORT_RE.test(desc);
      if (support) return (/^(harden|swords-dance|agility|double-team|nasty-plot|toxic-spikes|toxic)$/.test(id) ? 560 : 300) - index * 0.1;
      return (dmgMoves < 2 ? 850 : 800) - index * 0.1;
    }
    if (type === 'up') {
      const m = tag.match(/(\d+)\s*>/), lv = m ? Number(m[1]) : 0;
      if (recoil) return 100 - index * 0.1;
      const mv = pmoves.find(q => String(q.id) === id);
      const dmgUp = mv ? isDmgMove(mv) : !(noDmg || SUPPORT_RE.test(desc));
      return (dmgUp ? 650 : 420) + lv * 10 - index * 0.1;
    }
    if (type === 'stat') {
      const sid = key.replace('stat:', '');
      // v0.8.2: theo trận chơi tay: Vigor 73%, Power 65%, Learning 67%, Armor 33%, Magnet 38%, Synthesis 19%, Reflexes 15%, Sprint 0%
      const table = { hp: 560, atk: 500, xp: 480, mag: 330, def: 320, rgn: 230, cd: 210, spd: 40 };
      return (table[sid] ?? 100) - index * 0.1;
    }
    return 100 - index * 0.1;
  }

  function makeStatusCounts(P) {
    return {
      enemies: safe(() => P.EnemyMgr.all().length, 0),
      shots: safe(() => P.Projectiles.all().length, 0)
    };
  }

  // ===== v0.9.1: LƯU BÁO CÁO VÁN vào IndexedDB (lịch sử + điểm lưu giữa ván) =====
  const REP = { db: null };
  function repDb() {
    return new Promise(res => {
      if (REP.db) return res(REP.db);
      try {
        const rq = indexedDB.open('plh_reports', 1);
        rq.onupgradeneeded = () => { try { rq.result.createObjectStore('r', { keyPath: 'id' }); } catch (_) {} };
        rq.onsuccess = () => { REP.db = rq.result; res(REP.db); };
        rq.onerror = () => res(null);
      } catch (_) { res(null); }
    });
  }
  async function repPut(rec) { const db = await repDb(); if (!db) return false; return new Promise(r => { try { const tx = db.transaction('r', 'readwrite'); tx.objectStore('r').put(rec); tx.oncomplete = () => r(true); tx.onerror = tx.onabort = () => r(false); } catch (_) { r(false); } }); }
  async function repAll() { const db = await repDb(); if (!db) return []; return new Promise(r => { try { const rq = db.transaction('r').objectStore('r').getAll(); rq.onsuccess = () => r(rq.result || []); rq.onerror = () => r([]); } catch (_) { r([]); } }); }
  async function repGet(id) { const db = await repDb(); if (!db) return null; return new Promise(r => { try { const rq = db.transaction('r').objectStore('r').get(id); rq.onsuccess = () => r(rq.result || null); rq.onerror = () => r(null); } catch (_) { r(null); } }); }
  async function repDel(id) { const db = await repDb(); if (!db) return false; return new Promise(r => { try { const tx = db.transaction('r', 'readwrite'); tx.objectStore('r').delete(id); tx.oncomplete = () => r(true); tx.onerror = tx.onabort = () => r(false); } catch (_) { r(false); } }); }
  async function repList() { return (await repAll()).filter(x => x.id !== 'ckpt').sort((a, b) => b.startedAt - a.startedAt); }
  async function repPrune(max = 15) { const list = await repList(); for (const x of list.slice(max)) await repDel(x.id); }
  function stampOf(startedAt) { const d = new Date(startedAt); return `${d.getFullYear()}${String(d.getMonth() + 1).padStart(2, '0')}${String(d.getDate()).padStart(2, '0')}-${String(d.getHours()).padStart(2, '0')}${String(d.getMinutes()).padStart(2, '0')}${String(d.getSeconds()).padStart(2, '0')}`; }
  function saveText(text, startedAt) {
    try {
      const b = new Blob([text], { type: 'text/plain;charset=utf-8' }), a = document.createElement('a');
      a.href = URL.createObjectURL(b); a.download = `pokelit-run-${stampOf(startedAt)}.txt`; document.body.appendChild(a); a.click();
      setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 2000);
    } catch (e) { console.error(`${TAG} Không tự động tải file được trên thiết bị này`, e); }
  }
  async function downloadReportById(id) {
    const rec = await repGet(id);
    if (!rec) { showPanelMessage('Không tìm thấy báo cáo này.', true); return; }
    saveText(rec.text, rec.startedAt);
  }
  // ván bị ngắt giữa chừng (tải lại trang / iOS đóng app): điểm lưu cuối cùng được đưa vào lịch sử
  (async function recoverCheckpoint() {
    return;   // Lite: không có báo cáo
    try {
      const rec = await repGet('ckpt'); if (!rec) return;
      if (rec.dur >= 10) { rec.id = rec.startedAt; rec.reason = 'gián đoạn (tải lại trang / đóng app)'; await repPut(rec); }
      await repDel('ckpt'); await repPrune(15);
      W.dispatchEvent(new CustomEvent('plh-reports'));
    } catch (_) {}
  })();

  function installRunLog() {
    const ring = [];       // nhật ký đổi trạng thái game (để biết vì sao một ván bị cắt)
    let lastDead = false;
    const frag = { n: 0 };
    let run = null;
    let lastReport = null;
    let lastState = '', finishPending = 0;
    let prevEnemiesCount = 0;

    const recentRuns = () => safe(() => JSON.parse(localStorage.getItem('plh_runs') || '[]'), []);
    const nowSec = r => Math.max(0, (Date.now() - r.startedAt) / 1000);
    const modeName = P => safe(() => P.Rift.inArena, false) ? 'arena' : botMode;
    const gameTime = P => safe(() => Number(P.Game.st.time) || 0, 0);

    const hazardDistance = (h, x, y) => {
      const hx = Number(h.x ?? h.cx ?? h.centerX), hy = Number(h.y ?? h.cy ?? h.centerY);
      if (!Number.isFinite(hx) || !Number.isFinite(hy)) return Infinity;
      if (String(h.kind || h.type || '').toLowerCase().includes('beam')) {
        const len = Number(h.len ?? h.length) || 360, ang = Number(h.angle) || 0, ex = hx + Math.cos(ang) * len, ey = hy + Math.sin(ang) * len, dx = ex - hx, dy = ey - hy, t = clamp(((x - hx) * dx + (y - hy) * dy) / (dx * dx + dy * dy || 1), 0, 1);
        return Math.max(0, Math.hypot(x - (hx + t * dx), y - (hy + t * dy)) - (Number(h.w) || 20) / 2);
      }
      return Math.max(0, Math.hypot(x - hx, y - hy) - (Number(h.r ?? h.radius) || 48));
    };

    const snap = (P, p) => {
      const enemies = safe(() => P.EnemyMgr.all(), []) || [];
      const pickups = safe(() => P.Pickups.all(), []) || [];
      const allProjectiles = safe(() => P.Projectiles.all(), []) || [], shots = allProjectiles.filter(q => isEnemyProjectile(q, p));
      const hazards = safe(() => { const a = P.Hazards.all; return typeof a === 'function' ? a.call(P.Hazards) : a; }, []) || [];
      return {
        enemies, pickups, shots, allProjectiles, hazards, hp: Number(p.hp) || 0, x: Number(p.x) || 0, y: Number(p.y) || 0,
        gameSec: gameTime(P), realSec: nowSec(run), mode: modeName(P), hpPct: p.maxHp ? 100 * p.hp / p.maxHp : 0
      };
    };

    function begin(P, p) {
      const now = Date.now();
      const st = safe(() => P.Game.st, {});
      logOnce('gameSt', 'Game.st keys/sample:', { keys: Object.keys(st || {}), sample: plain(st) });

      const options = [['player.name', p.name], ['player.species', p.species], ['player.dex', p.dex], ['Game.st.pokemon', st?.pokemon], ['Game.st.species', st?.species], ['Game.st.dex', st?.dex]];
      const selected = options.find(([, v]) => typeof v === 'string' && v.trim()) || options.find(([, v]) => v !== undefined && v !== null);
      const domName = safe(() => document.querySelector('[class*="pokemon"], [class*="player-name"], header h1')?.textContent?.trim(), '');
      const dexName = safe(() => p.mon?.name || P.Pokemon?.[p.dex]?.name || P.Pokedex?.[p.dex]?.name || P.Game.st?.pokemon?.name || P.Game.st?.species?.name, '');
      const species = selected && typeof selected[1] === 'string' ? selected[1] : dexName || domName || (p.dex != null ? `dex ${p.dex}` : '');
      const speciesSource = selected && typeof selected[1] === 'string' ? selected[0] : dexName ? 'P.Pokemon/Pokedex or Game.st' : 'DOM/dex fallback';

      run = {
        version: VERSION, ticketStart: safe(() => ({ t1: P.DB.save.tickets.t1, t10: P.DB.save.tickets.t10 }), null), startedAt: now, endedAt: null, pokemon: { dex: p.dex ?? null, name: species || '?', nameSource: speciesSource },
        settings: { ...state, autoDownload: reportPrefs.autoDownload }, timeline: [],
        damage: { byType: { 'chạm quái': 0, 'đạn': 0, 'vùng': 0, 'khác': 0 }, hits: [] },
        xp: { collected: 0, left: 0, perMinute: 0 }, waterSeconds: 0, stuckCount: 0, unsticks: [], titan: [], chestEv: {}, hazardDodges: 0, hazardKinds: {}, sharpTurns: 0, cards: [], kills: 0,
        rifts: [], events: [], freezes: [], lastSevenSeconds: [], issues: [], timelineBot: [], arenaHits: [], arenaBossLogs: [], unknownSources: [], samples: sampleData
      };
      chestMem.clear(); chestTrack.clear(); propBlacklist.clear(); mapMem = new Map(); hunt.visited.clear(); hunt.nearSince.clear(); hunt.exTarget = null;
      badCells.clear(); huntFails.clear(); routeCache.clear(); coopSeen.clear(); huntStats.active = 0; huntStats.opened = 0; huntStats.goals = 0; huntStats.maxKnown = 0; scanDone.clear(); scanQueue = []; trail.clear(); wideEvery = 0; lastWideScan = 0;
      run._sawOver = false; run._ckptAt = Date.now(); run._offAt = 0;
      run._prev = null; run._lastTimeline = -5; run._lastSample = now; run._inWater = null; run._stuckSince = null; run._stuckCounted = false; run._stuckOrigin = null; run._lastPos = null; run._lastDir = null;
      run._seenRift = false; run._arenaAt = null; run._wasArena = false; run._prevActive = p.active;
      run._xpCurrent = Number(p.xp) || 0; run._xpNext = Number(p.xpNext) || 0; run._xpLevel = Number(p.level) || 1; run._xpTotal = 0;
      run._prevLevel = Number(p.level) || 1;
      run._prevSlotsState = safe(() => JSON.stringify((p.slots || p.moves || []).map(m => ({ name: m.name || m.id || m.def?.name || m.key, lvl: m.lvl || m.level || 1 }))), '');
      prevEnemiesCount = 0;
      const s = snap(P, p); run._prev = s;
      W.__PLH_RUN_LOG = { recordStuck: (m) => { if (run) run.stuckCount++; }, recordUnstick: (u) => { if (run) { run.stuckCount++; if (run.unsticks.length < 60) run.unsticks.push({ t: Math.round((Date.now() - run.startedAt) / 1000), ...u }); } }, recordCoop: (n, host) => { if (run) { run.coop = run.coop || { maxMates: 0, host: null, reviveGoals: 0, followGoals: 0 }; run.coop.maxMates = Math.max(run.coop.maxMates, n); run.coop.host = host; } }, recordShop: (t) => { if (run) { run.shop = run.shop || []; if (run.shop.length < 20) run.shop.push({ t: Math.round((Date.now() - run.startedAt) / 1000), what: t }); } }, recordCoopGoal: (k) => { if (run) { run.coop = run.coop || { maxMates: 0, host: null, reviveGoals: 0, followGoals: 0 }; run.coop[k] = (run.coop[k] || 0) + 1; } }, recordHazard: (k) => { if (run) { run.hazardDodges++; run.hazardKinds[k] = (run.hazardKinds[k] || 0) + 1; } }, recordTitan: (e) => { if (run) { run.titan = run.titan || []; if (run.titan.length < 120) run.titan.push({ t: Math.round((Date.now() - run.startedAt) / 1000), ...e }); } }, recordChestEv: (k) => { if (run) { run.chestEv = run.chestEv || {}; run.chestEv[k] = (run.chestEv[k] || 0) + 1; } } };
      console.info(`${TAG} Nhật ký trận bắt đầu (v${VERSION})`, { version: run.version, pokemon: run.pokemon, settings: run.settings });
    }

    function h0kind(s, p) { const h = s.hazards.find(h => hzContains(h, p.x, p.y, p.r || 10, 8)); return h && h.kind === 'beam' ? 'vùng (tia boss)' : 'vùng'; }
    function classifyDamage(P, s, amount, p) {
      try {
        for (const q of s.shots) {
          for (let t = 0; t <= .5; t += .1) {
            const x = q.x + (q.vx || 0) * t, y = q.y + (q.vy || 0) * t;
            if (Math.hypot(x - p.x, y - p.y) < (q.r || 8) + (p.r || 10) + 14) return 'đạn';
          }
        }
      } catch (_) {}
      try { if (s.hazards.some(h => hzContains(h, p.x, p.y, p.r || 10, 8))) return h0kind(s, p); } catch (_) {}
      try { const near = s.enemies.some(e => Math.hypot(e.x - p.x, e.y - p.y) < (e.r || 10) + (p.r || 10) + 20); if (near) return 'chạm quái'; } catch (_) {}
      return 'khác';
    }

    function unknownSourceSample(s, p) {
      const list = [];
      for (const q of s.allProjectiles || []) list.push({ kind: 'projectile', d: Math.hypot(q.x - p.x, q.y - p.y), keys: Object.keys(q || {}), sample: plain(q) });
      for (const h of s.hazards || []) list.push({ kind: 'hazard', d: hazardDistance(h, p.x, p.y), keys: Object.keys(h || {}), sample: plain(h) });
      for (const e of s.enemies || []) list.push({ kind: 'enemy', d: Math.hypot(e.x - p.x, e.y - p.y), keys: Object.keys(e || {}), sample: plain(e) });
      return list.sort((a, b) => a.d - b.d).slice(0, 5);
    }

    function issues(r) {
      const types = r.damage.byType; const main = Object.entries(types).sort((a, b) => b[1] - a[1])[0];
      const elapsed = Math.max(1, nowSec(r)); r.xp.perMinute = r.xp.collected / elapsed * 60;
      const flags = [];
      if (main && main[1] > 0) flags.push(`Nguồn sát thương chính: ${main[0]} (${main[1].toFixed(1)} HP).`);
      if (r.stuckCount >= 3) flags.push(`Kẹt nhiều: ${r.stuckCount} lần.`);
      if (r.xp.left > r.xp.collected) flags.push(`Bỏ lại nhiều XP: ${r.xp.left} còn trên bản đồ, ${r.xp.collected} nhặt được.`);
      if (r.xp.perMinute < 20) flags.push(`XP/phút thấp: ${r.xp.perMinute.toFixed(1)}.`);
      if (r.sharpTurns >= 8) flags.push(`Đổi hướng gấp nhiều: ${r.sharpTurns} lần.`);
      if (r.freezes.length) flags.push(`Đứng hình: ${r.freezes.length} khoảng lấy mẫu bị gián đoạn trên 1 giây.`);
      const fatal = r.damage.hits.slice().sort((a, b) => b.amount - a.amount)[0];
      if (fatal) flags.push(`Cú mất HP lớn nhất lúc ${fmt(fatal.realSec)} (${fatal.source}, mode ${fatal.mode}).`);
      r.issues = flags.length ? flags : ['Không phát hiện vấn đề nổi bật theo các ngưỡng cơ bản.'];
    }

    function fmt(seconds) { const n = Math.max(0, Math.floor(seconds)); return `${String(Math.floor(n / 60)).padStart(2, '0')}:${String(n % 60).padStart(2, '0')}`; }

    function human(r) {
      const lines = [
        `PokéLit Bot — Báo cáo trận v${VERSION}`,
        `Pokémon: ${r.pokemon.name || 'unknown'} (dex ${r.pokemon.dex ?? '?'}, nguồn ${r.pokemon.nameSource})`,
        `Thời lượng: ${fmt((r.endedAt - r.startedAt) / 1000)}; level cuối ${r.final?.level ?? '?'}; hạ quái: ${r.kills ?? 0}`,
        `TÓM TẮT: sát thương nhận ${Object.values(r.damage.byType).reduce((a, b) => a + b, 0).toFixed(0)} (từ vùng/tia: ${Object.entries(r.damage.byType).filter(([k]) => k.startsWith('vùng')).reduce((a, [, v]) => a + v, 0).toFixed(0)}); kẹt/thoát kẹt ${r.stuckCount} lần; né vùng chủ động ${r.hazardDodges || 0} lần`,
        '', 'VẤN ĐỀ PHÁT HIỆN', ...r.issues.map(x => `• ${x}`),
        '',
        `Sát thương nhận: ${Object.entries(r.damage.byType).map(([k, v]) => `${k} ${v.toFixed(1)}`).join(' | ')}`,
        `XP nhặt: ${r.xp.collected}; XP còn lại: ${r.xp.left}; XP/phút: ${r.xp.perMinute.toFixed(1)}`,
        ...(r.unsticks?.length ? ['THOÁT KẸT (giây | mức | vị trí | mục tiêu | lý do)', ...r.unsticks.map(u => `${fmt(u.t)} | mức ${u.level} | ${u.x},${u.y} | ${u.goal || '-'} | ${u.reason || 'đứng yên ' + u.moved + 'px'}`)] : []),
        ...(r.coop ? [`CO-OP: ${r.coop.host ? 'chủ phòng' : 'khách'}; đồng đội tối đa ${r.coop.maxMates}; lần đi hồi sinh ${r.coop.reviveGoals || 0}; lần bám đồng đội ${r.coop.followGoals || 0}; lần đứng giữ cạnh xác ${r.coop.holds || 0}; đồng đội được hồi sinh ${r.coop.revived || 0}; (không ghi dữ liệu học trong co-op)`] : []),
        `Vé hiện có: ×1 ${safe(() => W.__PL.DB.save.tickets.t1, '?')}, ×10 ${safe(() => W.__PL.DB.save.tickets.t10, '?')} (lúc bắt đầu trận: ×1 ${r.ticketStart?.t1 ?? '?'}, ×10 ${r.ticketStart?.t10 ?? '?'})`,
        ...(r.shop?.length ? ['KECLEON: ' + r.shop.map(x => `${fmt(x.t)} ${x.what}`).join(' | ')] : []),
        ...(r.titan?.length ? ['TITAN (giây | sự kiện | chi tiết)', ...r.titan.map(x => `${fmt(x.t)} | ${x.e} | ${x.e === 'nova' ? (x.safe ? (x.inside ? 'có vòng an toàn: ĐỨNG TRONG vòng lúc nổ' : 'có vòng an toàn: ĐỨNG NGOÀI vòng lúc nổ') : 'KHÔNG có vòng an toàn') + `, HP ${x.hp}%` : x.e === 'phase' ? `pha ${x.ph}, Titan còn ${x.bh}% máu` : `pha ${x.ph}, Titan còn ${x.bh}% máu, HP bạn ${x.hp}%`}`)] : []),
        ...(r.chestEv && Object.keys(r.chestEv).length ? ['KẾT QUẢ ĐI TỚI HÒM: ' + JSON.stringify(r.chestEv)] : []),
        `Né vùng chủ động: ${r.hazardDodges || 0} ${JSON.stringify(r.hazardKinds || {})}`,
        `Kẹt: ${r.stuckCount}; đổi hướng gấp: ${r.sharpTurns}; thời gian nước: ${r.waterSeconds.toFixed(1)}s`,
        `Kết thúc ván: ${r.reason || '?'}`,
        ...(r.chest ? [`HÒM: biết tối đa ${r.chest.known}; đã mở/đập ${r.chest.opened}; lần đi tới hòm ${r.chest.goals}; (săn hòm toàn map: ${r.settings?.chestHunt ? 'bật' : 'tắt'}, phạm vi ${r.settings?.chestRange ?? '?'}px)`] : []),
        ...(r.perf ? [`HIỆU NĂNG: AI trung bình ${r.perf.avg.toFixed(1)}ms/lần, đỉnh ${r.perf.max.toFixed(1)}ms; ${r.perf.fps} FPS; đã bỏ qua ${r.perf.skipped} / ${r.perf.calls + r.perf.skipped} lần gọi; quét hòm: ${r.perf.scanned ?? '?'} ô, lần cuối ${r.perf.wideMs.toFixed(1)}ms, phạm vi ${r.perf.wideR}px`] : []),
        ...(r.stateLog?.length ? ['CHUYỂN TRẠNG THÁI GAME (giây từ đầu ván | chuyển | gục? | giờ game)', ...r.stateLog.slice(0, 60).map(x => `${fmt(x.t)} | ${x.s} | ${x.dead ? 'gục' : '-'} | ${x.g}s`)] : []),
        '', 'DÒNG THỜI GIAN (mỗi 2s)',
        ...(r.timelineBot || []).map(t => `${fmt(t.realSec)} | HP ${t.hpPct.toFixed(1)}% | ${t.mode} | ở ${t.pos || '?'} đi ${t.dir || '?'} | mục tiêu: ${t.target || 'không có'} (${t.targetPos || '—'})${t.goalDist != null ? ` cách ${t.goalDist}px, đường ${t.path}` : ''} | lý do: ${t.reason || '—'} | quái 150px: ${t.nearby}`),
        '', 'LỐI DI CHUYỂN (vị trí mỗi 1s; B = bot lái, N = bạn tự lái)',
        ...(() => { const out = [], tr = r.track || []; for (let i = 0; i < tr.length; i += 15) { const ch = tr.slice(i, i + 15); out.push(`${fmt(ch[0][0])} ` + ch.map(q => `${q[3]}${q[1]},${q[2]}`).join(' ')); } return out; })(),
        '', 'HỌC TỪ NGƯỜI CHƠI',
        `Mẫu di chuyển đã ghi: ${r.learnInfo?.total ?? 0} (trận này thêm ${r.learnInfo?.thisRun ?? 0}); dùng khi chạy bot: ${r.learnInfo?.use ? 'bật' : 'tắt'}, mức ${r.learnInfo?.mix ?? '?'}`,
        ...(r.learnInfo?.pools ? PHASES.map((nm, i) => `   ${nm}: đã ghi ${r.learnInfo.seen?.[i] ?? 0}, bot đang dùng ${r.learnInfo.pools[i]}`) : []),
        `Bạn tự lái: ${(r.manualSec || 0).toFixed(0)}s; bot lái: ${(r.botSec || 0).toFixed(0)}s`,
        ...Object.entries(r.learnInfo?.cards || {}).sort((a, b) => b[1].o - a[1].o).slice(0, 25).map(([k, v]) => `• ${k}: bạn chọn ${v.c}/${v.o} lần (${Math.round(100 * v.c / Math.max(1, v.o))}%)`),
        '', 'THẺ ĐÃ CHỌN VÀ ĐỀ NGHỊ',
        `Tự chọn thẻ: ${r.settings?.enabled ? 'bật (theo công tắc Bot)' : 'TẮT (Bot tắt, bạn tự chọn)'}; ưu tiên chỉ số: ${(r.settings?.priorities || []).join(', ')}; reroll khi < ${r.settings?.rerollThreshold ?? 150}đ`,
        `Chiêu hiện có: ${r.movesNow || '?'}`,
        '',
        'CÁC CÚ MẤT HP LỚN NHẤT',
        ...(r.damage?.hits || []).slice().sort((a, b) => b.amount - a.amount).slice(0, 15).map(h => `${fmt(h.realSec)} −${h.amount.toFixed(1)} HP${h.pct != null ? ` (${h.pct}% máu tối đa)` : ''} | ${h.source} | mode ${h.mode} | quái gần: ${h.att || '-'} | đạn gần: ${h.shotD || '-'}px`),
        '',
        ...(r.cards || []).map((c, i) => `${i + 1}. Lv${c.level ?? '?'} ${fmt(c.realSec)} | HP ${c.hpPct ?? '?'}% | Đề nghị: [${(c.offered || []).map(o => `${o.name} {${o.cls || o.type}} ${o.score ?? '?'}đ${o.learned ? ` (học ${o.learned > 0 ? '+' : ''}${o.learned})` : ''}`).join(' | ')}] | Chọn: ${c.chosenName} — ${c.reason}${c.reroll ? ' (dùng reroll)' : ''}`),
        '', '7 GIÂY CUỐI',
        ...(r.lastSevenSeconds || []).map(s => `${fmt(s.realSec)} HP ${s.hp.toFixed(1)} (${s.damageSource || '—'}) @ (${s.x.toFixed(0)},${s.y.toFixed(0)}) ${s.mode}; gần nhất name=${s.closest?.name || '?'} dist=${s.closest?.d?.toFixed(0) || '?'}; quái: ${s.enemies.map(e => `${e.name || '?'}(${e.d.toFixed(0)}px)`).join(', ')}`),
        '', 'MẪU DỮ LIỆU THU THẬP ĐƯỢC',
        ...Object.values(r.samples || {})
      ];
      return lines.join('\n');
    }

    function download(r, quiet) {
      const content = typeof r === 'string' ? r : human(r);
      if (!quiet) showReportFallback(content);
      saveText(content, typeof r === 'string' ? Date.now() : r.startedAt);
    }

    function finish(P, p, reason) {
      if (!run) return;
      const durSec = (Date.now() - run.startedAt) / 1000;
      if (durSec < 10) { frag.n++; console.info(`${TAG} Bỏ mảnh ván ${durSec.toFixed(1)}s (${reason}) — không lưu, không tải`); run = null; return; }
      const s = snap(P, p);
      const finalXp = Number(p.xp) || 0, finalLevel = Number(p.level) || run._xpLevel;
      if (finalLevel > run._xpLevel) run.xp.collected += Math.max(0, run._xpNext - run._xpCurrent) + finalXp;
      else run.xp.collected += Math.max(0, finalXp - run._xpCurrent);
      run.xp.left = s.pickups.filter(x => String(x.kind).toLowerCase().includes('xp')).reduce((n, x) => n + (Number(x.value) || 1), 0);

      run.reason = reason || '?';
      run.chest = { known: huntStats.maxKnown || chestMem.size, opened: huntStats.opened, goals: huntStats.goals };
      run.perf = { avg: perf.avg, max: perf.max, fps: perf.fps, skipped: perf.skipped, calls: perf.calls, wideMs: perf.wideMs, wideR: huntStats.wideR, scanned: scanDone.size };
      run.stateLog = ring.filter(x => x.t >= run.startedAt - 3000).map(x => ({ t: Math.max(0, (x.t - run.startedAt) / 1000), s: x.s, dead: x.dead, g: x.g }));
      run.endedAt = Date.now();
      run.xp.perMinute = run.xp.collected / Math.max(1, (run.endedAt - run.startedAt) / 60000);
      run.final = { gameSec: s.gameSec, hp: s.hp, mode: s.mode, x: s.x, y: s.y, level: p.level, lifetimeSec: (run.endedAt - run.startedAt) / 1000 };
      const lastHit = run.damage.hits.at(-1);
      run.death = { realSec: lastHit?.realSec || s.realSec, source: lastHit?.source || 'không xác định', mode: lastHit?.mode || s.mode };

      issues(run);
      run.samples = { ...sampleData };

      const summary = { startedAt: run.startedAt, endedAt: run.endedAt, pokemon: run.pokemon, durationSec: (run.endedAt - run.startedAt) / 1000, damage: run.damage.byType, xp: run.xp, kills: run.kills, stuckCount: run.stuckCount, sharpTurns: run.sharpTurns, issues: run.issues, final: run.final };
      try { const arr = recentRuns(); arr.unshift(summary); localStorage.setItem('plh_runs', JSON.stringify(arr.slice(0, 10))); } catch (e) { console.warn(`${TAG} Không lưu được plh_runs`, e); }

      for (const key of Object.keys(run)) if (key.startsWith('_')) delete run[key];
      run.learnInfo = { pools: learn.pools.map(p => p.length), seen: learn.seen.slice(), total: learn.total, thisRun: learn.runMoves, use: state.learnUse, mix: state.learnMix, cards: JSON.parse(JSON.stringify(learn.cards)) }; learn.runMoves = 0; saveLearn(true);
      lastReport = plain(run);
      try { localStorage.setItem('plh_latest_report', JSON.stringify(lastReport)); } catch (_) {}
      // v0.9.1: lưu mọi ván vào lịch sử; CHỈ tự tải file khi ván kết thúc hẳn (hết ván), không tải khi vào rift hay mảnh ngắn
      try {
        const text = human(lastReport);
        const rec = { id: lastReport.startedAt, startedAt: lastReport.startedAt, endedAt: lastReport.endedAt, dur: durSec, level: lastReport.final?.level ?? null, kills: lastReport.kills ?? 0, reason: lastReport.reason, text };
        repPut(rec).then(() => repDel('ckpt')).then(() => repPrune(15)).then(() => W.dispatchEvent(new CustomEvent('plh-reports')));
        if (lastReport.reason === 'over' && reportPrefs.autoDownload) setTimeout(() => { try { saveText(text, rec.startedAt); } catch (e) { showReportFallback(String(e)); } }, 500);
      } catch (e) { console.warn(`${TAG} Không lưu được báo cáo`, e); }
      console.info(`${TAG} Trận kết thúc (${reason})`, summary); run = null;
    }

    function liveTmp(reason) {
      const P = W.__PL, pl = P?.Game?.player || {};
      const tmp = Object.assign({}, run, { endedAt: Date.now(), reason });
      tmp.final = { level: pl.level ?? null, hp: pl.hp, gameSec: gameTime(P), lifetimeSec: (Date.now() - run.startedAt) / 1000 };
      tmp.chest = { known: huntStats.maxKnown || chestMem.size, opened: huntStats.opened, goals: huntStats.goals };
      tmp.perf = { avg: perf.avg, max: perf.max, fps: perf.fps, skipped: perf.skipped, calls: perf.calls, wideMs: perf.wideMs, wideR: huntStats.wideR, scanned: scanDone.size };
      issues(tmp); return tmp;
    }
    function checkpoint(P) {
      try {
        if (!run) return;
        const tmp = liveTmp('đang chạy (điểm lưu)');
        const text = human(tmp);
        repPut({ id: 'ckpt', startedAt: run.startedAt, endedAt: tmp.endedAt, dur: (tmp.endedAt - run.startedAt) / 1000, level: Number(P.Game.player?.level) || null, kills: run.kills, reason: tmp.reason, text });
      } catch (_) {}
    }

    function sample() {
      try {
        const P = W.__PL; if (!P?.Game?.player) return;
        const p = P.Game.player, currentState = P.Game.state, nowT = Date.now();
        const gameT = Number(safe(() => P.Game.st.time, 0)) || 0;
        if (currentState !== lastState || !!p.dead !== lastDead) {
          ring.push({ t: nowT, s: `${lastState || '∅'}→${currentState}`, dead: !!p.dead, g: Math.round(gameT) }); if (ring.length > 80) ring.shift();
          lastDead = !!p.dead;
        }
        // Ván mới nhưng ván cũ chưa kịp chốt (tự chơi lại rất nhanh): chốt ván cũ theo cách nó đã kết thúc
        const timeBack = run && run._lastGameT != null && gameT + 3 < run._lastGameT && gameT < 10;
        if (run && currentState === 'playing' && timeBack) finish(P, run._lastP || p, run._sawOver ? 'over' : 'đổi ván');
        if (!run && currentState === 'playing') begin(P, p);
        lastState = currentState;
        if (!run) return;
        run._lastGameT = gameT;
        run._lastP = { xp: p.xp, level: p.level, hp: p.hp, maxHp: p.maxHp, x: p.x, y: p.y, r: p.r, id: p.id, dex: p.dex, dead: false };
        huntStats.maxKnown = Math.max(huntStats.maxKnown || 0, chestMem.size);

        // v0.9.1: chỉ chốt báo cáo khi game báo 'over' ổn định ≥1.5s (không còn dựa vào p.dead — co-op gục/hồi sinh làm cắt ván thành nhiều mảnh)
        if (currentState === 'over') {
          run._sawOver = true;
          if (!run._overAt) run._overAt = nowT;
          if (nowT - run._overAt >= 1500) finish(P, p, 'over');
          return;
        }
        run._overAt = 0;
        if (currentState !== 'playing' && currentState !== 'ui' && currentState !== 'paused' && currentState !== '') {
          if (!run._offAt) run._offAt = nowT;
          if (nowT - run._offAt > 4000) { finish(P, run._lastP || p, 'thoát'); return; }
        } else run._offAt = 0;
        if (currentState === 'playing' && nowT - run._ckptAt > 20000) { run._ckptAt = nowT; setTimeout(() => checkpoint(P), 0); }

        const s = snap(P, p), prev = run._prev, elapsed = (Date.now() - run._lastSample) / 1000;

        if (prevEnemiesCount > 0 && s.enemies.length < prevEnemiesCount) {
          run.kills += (prevEnemiesCount - s.enemies.length);
        }
        prevEnemiesCount = s.enemies.length;

        // BÁO CÁO "THẺ ĐÃ CHỌN": LẤY TÊN VÀ LEVEL CHUẨN TỪ move.name VA move.lvl
        const curLevel = Number(p.level) || 1;
        const rawMoves = safe(() => (p.moves || p.slots || []).map(m => ({
          name: m.name || m.id || m.def?.name || m.key || 'Skill',
          lvl: m.lvl || m.level || 1
        })), []);
        const curMovesState = JSON.stringify(rawMoves);

        if (curLevel > run._prevLevel || curMovesState !== run._prevSlotsState) {
          const moveNamesStr = rawMoves.map(m => `${m.name}(lv${m.lvl})`).join(', ') || 'Cập nhật kỹ năng';
          run.movesNow = moveNamesStr;
          if (false) {
            run.cards.push({
              realSec: s.realSec,
              level: curLevel,
              offered: [],
              chosenName: moveNamesStr,
              score: 0,
              reason: curLevel > run._prevLevel ? 'Lên cấp' : 'Cập nhật kỹ năng'
            });
          }
          run._prevLevel = curLevel;
          run._prevSlotsState = curMovesState;
        }

        if (prev && elapsed > 1) run.freezes.push({ realSec: s.realSec, gameSec: s.gameSec, gapSec: elapsed });

        if (prev && p.hp < prev.hp) {
          const amount = prev.hp - p.hp, source = classifyDamage(P, s, amount, p);
          let bucket = source === 'vùng' ? 'vùng' : source;
          if (source === 'khác' && amount > 0.2 * (p.maxHp || 1)) bucket = 'mất máu lớn không rõ';   // v0.9.2: tách các lần mất >20% máu tối đa không rõ nguồn (định kỳ?)
          run.damage.byType[bucket] = (run.damage.byType[bucket] || 0) + amount;
          const att = (s.enemies || []).map(e => ({ n: e.name, b: e.behavior, ph: e.phase, d: Math.hypot(e.x - p.x, e.y - p.y) })).sort((a, b) => a.d - b.d)[0];
          const shotD = (s.shots || []).map(q => Math.hypot(q.x - p.x, q.y - p.y)).sort((a, b) => a - b)[0];
          run.damage.hits.push({ realSec: s.realSec, gameSec: s.gameSec, amount, pct: Math.round(100 * amount / Math.max(1, p.maxHp || 1)), source, mode: s.mode, hp: p.hp, att: att ? `${att.n}/${att.b}/${att.ph || '-'}@${att.d.toFixed(0)}px` : '-', shotD: shotD != null ? shotD.toFixed(0) : '-' });
        }

        const xpNow = Number(p.xp) || 0, levelNow = Number(p.level) || run._xpLevel, xpNext = Number(p.xpNext) || 0;
        if (levelNow > run._xpLevel) run.xp.collected += Math.max(0, run._xpNext - run._xpCurrent) + xpNow;
        else run.xp.collected += Math.max(0, xpNow - run._xpCurrent);
        run._xpCurrent = xpNow; run._xpNext = xpNext; run._xpLevel = levelNow;

        if (p.inLiquid) { if (run._inWater === null) run._inWater = Date.now(); }
        else if (run._inWater !== null) { run.waterSeconds += (Date.now() - run._inWater) / 1000; run._inWater = null; }

        if (!run.track) run.track = [];
        if (!run._lastTrack || s.realSec - run._lastTrack >= 1) { run.track.push([s.realSec, Math.round(p.x), Math.round(p.y), state.enabled ? 'B' : 'N']); run._lastTrack = s.realSec; }
        if (prev && elapsed < 1) { if (state.enabled) run.botSec = (run.botSec || 0) + elapsed; else run.manualSec = (run.manualSec || 0) + elapsed; }
        if (s.realSec - run._lastTimeline >= 2) {
          const goalPosStr = goalState.goal ? `(${goalState.goal.x.toFixed(0)},${goalState.goal.y.toFixed(0)})` : '—';
          const g = goalState.goal, botOn = state.enabled;
          run.timelineBot.push({
            realSec: s.realSec, gameSec: s.gameSec, hpPct: s.hpPct, mode: s.mode,
            pos: `(${p.x.toFixed(0)},${p.y.toFixed(0)})`, dir: ['→','↘','↓','↙','←','↖','↑','↗','•'][dirOfVec(botVector[0] || 0, botVector[1] || 0)],
            goalDist: botOn && g ? Math.round(Math.hypot(g.x - p.x, g.y - p.y)) : null,
            path: botOn && g ? (pathCache.reachable ? 'ok' : 'KHÔNG TÌM ĐƯỢC') : null,
            target: botOn ? currentTarget : 'bạn tự đi', targetPos: botOn ? goalPosStr : '—', reason: botOn ? targetReason : '—',
            nearby: s.enemies.filter(e => Math.hypot(e.x - p.x, e.y - p.y) < 150).length
          });
          run._lastTimeline = s.realSec;
        }

        // v0.9.1: không sao chép/sắp xếp toàn bộ quái mỗi lần lấy mẫu — chỉ chọn quái gần nhất và 6 quái gần
        let closest = null; const top = [];
        for (const e of s.enemies) {
          const d = Math.hypot(e.x - p.x, e.y - p.y);
          if (!closest || d < closest.d) closest = { name: e.name, d, behavior: e.behavior, dmg: e.dmg, spd: e.spd };
          if (top.length < 6 || d < top[top.length - 1].d) {
            const ent = { name: e.name, d, behavior: e.behavior, boss: !!e.boss }; let k = top.length; top.push(ent);
            while (k > 0 && top[k - 1].d > d) { top[k] = top[k - 1]; k--; }
            top[k] = ent; if (top.length > 6) top.pop();
          }
        }
        const recentHit = run.damage.hits.at(-1);
        run.lastSevenSeconds.push({
          realSec: s.realSec, gameSec: s.gameSec, hp: s.hp, x: s.x, y: s.y, mode: s.mode,
          damageSource: recentHit && s.realSec - recentHit.realSec < .3 ? recentHit.source : null,
          closest,
          enemies: top,
          shots: s.shots.filter(q => Math.hypot(q.x - p.x, q.y - p.y) <= 300).length,
          hazardNear: s.hazards.filter(h => hazardDistance(h, p.x, p.y) < 150).length
        });
        run.lastSevenSeconds = run.lastSevenSeconds.filter(x => s.realSec - x.realSec <= 7);

        run._prev = s; run._lastSample = Date.now();
      } catch (e) { console.warn(`${TAG} Lỗi nhật ký (đã bỏ qua mẫu)`, e); }
    }

    function recordCardSelection(offeredOptions, chosenOption, score, reason, reroll, level, allScores) {
      try {
        if (run) {
          const offeredList = (offeredOptions || []).map(o => ({
            name: o?.name || o?.title || o?.id || o?.def?.name || o?.key || 'Unknown',
            type: o?.type || o?.kind || 'stat', cls: cardClasses(o)[0] || ''
          }));
          (allScores || []).forEach((sc, i) => { if (offeredList[i]) { offeredList[i].score = sc.base + sc.learned; offeredList[i].learned = sc.learned; } });
          const chosenName = chosenOption?.name || chosenOption?.title || chosenOption?.id || chosenOption?.def?.name || chosenOption?.key || String(chosenOption);
          run.cards.push({ realSec: nowSec(run), level, offered: offeredList, chosenName, score, reason, reroll: !!reroll, hpPct: safe(() => Math.round(100 * W.__PL.Game.player.hp / W.__PL.Game.player.maxHp), null) });
        }
      } catch (_) {}
    }

    function exportLatest() {
      try {
        if (run) {
          const tmp = liveTmp('đang chạy (xuất giữa ván)');
          download(tmp); return;
        }
        repList().then(list => {
          if (list[0]) { saveText(list[0].text, list[0].startedAt); showPanelMessage(`Đã tải ván gần nhất (${new Date(list[0].startedAt).toLocaleTimeString()}).`); return; }
          lastReport = lastReport || safe(() => JSON.parse(localStorage.getItem('plh_latest_report') || 'null'), null);
          if (lastReport) download(lastReport); else showReportFallback('Chưa có báo cáo. Hãy chơi xong một ván trước khi xuất.');
        });
      } catch (e) { showReportFallback('Lỗi xuất: ' + (e.message || e)); }
    }

    function compare() {
      try {
        const arr = recentRuns();
        const rows = arr.map((r, i) => `${i + 1}. ${r.pokemon?.name || '?'} — ${(r.durationSec / 60).toFixed(1)} phút; XP/phút ${Number(r.xp?.perMinute || 0).toFixed(1)}; kẹt ${r.stuckCount}; đổi hướng ${r.sharpTurns}; ${Object.entries(r.damage || {}).sort((a, b) => b[1] - a[1])[0]?.[0] || 'chưa rõ'} sát thương chính`).join('\n');
        showPanelMessage(arr.length ? `So sánh ${arr.length} trận gần nhất\n\n${rows}` : 'Chưa có dữ liệu trận.');
      } catch (e) { showPanelMessage('Lỗi so sánh: ' + (e.message || e), true); }
    }

    return {
      sample, recordCardSelection, exportLatest, compare, listReports: repList, downloadById: downloadReportById, fragments: () => frag.n,
      setAutoDownload(v) { reportPrefs.autoDownload = !!v; state.autoDownload = !!v; persistSettings(); },
      getAutoDownload() { return reportPrefs.autoDownload; }
    };
  }

  const runLog = { sample() {}, recordCardSelection() {}, exportLatest() {}, compare() {}, listReports: async () => [], downloadById() {} };   // Lite: không báo cáo

  function showPanelMessage(message, isError = false) {
    try {
      const panel = document.getElementById('plh-panel'); if (!panel) return;
      let box = panel.querySelector('#plh-message');
      if (!box) {
        box = document.createElement('div'); box.id = 'plh-message';
        box.style.cssText = 'margin-top:7px;padding:6px;background:#242938;border-radius:4px;white-space:pre-wrap;max-height:180px;overflow:auto';
        panel.appendChild(box);
      }
      box.textContent = message; box.style.color = isError ? '#ff5b5b' : '#fff';
      const close = document.createElement('button'); close.textContent = 'Đóng'; close.style.cssText = 'display:block;margin-top:5px';
      close.onclick = () => box.remove(); box.appendChild(close);
    } catch (_) {}
  }

  function showReportFallback(message) {
    try {
      const panel = document.getElementById('plh-panel'); if (!panel) return showPanelMessage(message, true);
      let box = panel.querySelector('#plh-report-fallback');
      if (!box) {
        box = document.createElement('div'); box.id = 'plh-report-fallback';
        box.style.cssText = 'margin-top:7px;padding:6px;background:#242938;border:1px solid #f55;border-radius:4px';
        const ta = document.createElement('textarea'); ta.id = 'plh-report-text';
        ta.style.cssText = 'width:100%;height:160px;box-sizing:border-box;font:11px monospace;background:#111;color:#fff';
        
        const copyBtn = document.createElement('button'); copyBtn.textContent = '📋 Copy báo cáo';
        copyBtn.style.cssText = 'display:block;margin-top:5px;width:100%;padding:6px;background:#3182ce;color:#fff;border:none;border-radius:4px';
        copyBtn.onclick = () => {
          try {
            if (navigator.clipboard && navigator.clipboard.writeText) {
              navigator.clipboard.writeText(ta.value).then(() => alert('Đã copy báo cáo!'));
            } else {
              ta.focus(); ta.select(); document.execCommand('copy'); alert('Đã copy báo cáo!');
            }
          } catch (_) { alert('Hãy chọn toàn bộ text và copy thủ công.'); }
        };
        box.append(ta, copyBtn); panel.appendChild(box);
      }
      const ta = box.querySelector('textarea');
      ta.value = message;
    } catch (_) {}
  }

  let yieldUntil = 0;
  function install(P) {
    if (!P || !P.Input || !P.Game || !P.Game.player) return false;

    if (!wrapped.axis && typeof P.Input.axis === 'function') {
      const original = P.Input.axis.bind(P.Input);
      P.Input.axis = function (...args) {
        if (!state.enabled) { botMode = 'bot-off'; botVector = safe(() => original(...args), [0, 0]); learnRecord(P, botVector); return botVector; }
        // v0.9.1: giãn nhịp tính hướng đi (mặc định ~30 lần/giây, tự giãn thêm nếu máy chậm); các khung hình giữa chừng dùng lại hướng gần nhất
        const t0 = performance.now(), nowMs = Date.now();
        if (state.yieldInput) {
          let man = null; try { man = original(...args); } catch (_) {}
          if (man && Math.hypot(man[0] || 0, man[1] || 0) > 0.01) { yieldUntil = nowMs + 900; }
          if (nowMs < yieldUntil) { botMode = 'bạn đang điều khiển'; return man || [0, 0]; }
        }
        if (state.perfMode && perf.lastThink && nowMs - perf.lastThink < perf.interval && nowMs - perf.lastThink >= 0) { perf.skipped++; return botVector; }
        const ctx = makeCtx(P);
        const t1 = performance.now();
        const v = think(ctx);
        botVector = v;
        perf.lastThink = nowMs; perf.calls++;
        const dt = performance.now() - t0;
        perf.avg = perf.avg ? perf.avg * 0.92 + dt * 0.08 : dt; perf.ctxAvg = perf.ctxAvg ? perf.ctxAvg * 0.92 + (t1 - t0) * 0.08 : (t1 - t0);
        if (dt > perf.winMax) perf.winMax = dt;
        if (nowMs - perf.winAt > 2000) { perf.max = perf.winMax; perf.winMax = 0; perf.winAt = nowMs; }
        perf.interval = perf.avg > 8 ? 66 : perf.avg > 4 ? 50 : 33;
        return v;
      };
      wrapped.axis = true;
    }

    if (!wrapped.level && P.RunUI && typeof P.RunUI.showLevelUp === 'function') {
      const originalShow = P.RunUI.showLevelUp.bind(P.RunUI);
      P.RunUI.showLevelUp = function (level, options, callback, ...rest) {
        if (Array.isArray(options) && options.length) {
          logOnce('showLevelUp_opts_' + (options || []).map(o => o.key).join('|'), 'Thẻ đề nghị:', (options || []).map(o => ({ type: o.type, key: o.key, title: o.title, tag: o.tag, desc: String(o.desc || '').slice(0, 90) })));
        }
        const offer = { level, options: Array.isArray(options) ? options : [], at: Date.now(), tries: 0, done: false, rerolled: false, lastTry: 0 };
        pendingCardOffer = offer;
        const wrappedCallback = function (choice, ...cbArgs) {
          try {
            const opts = offer.options || [];
            const idx = Math.max(0, opts.indexOf(choice));
            const allScores = opts.map((o, i) => ({ base: Math.round(scoreCardBase(o, i)), learned: learnCardBonus(o) }));
            if (!state.autoPick || !state.enabled) learnCardPick(opts, choice);
            runLog.recordCardSelection(opts, choice, Math.round(scoreCard(choice, idx)), (state.autoPick && state.enabled) ? 'bot chọn' : 'người chơi chọn', offer.rerolled, level, allScores);
          } catch (_) {}
          offer.done = true;
          if (pendingCardOffer === offer) pendingCardOffer = null;
          if (typeof callback === 'function') return callback(choice, ...cbArgs);
        };
        return originalShow(level, options, wrappedCallback, ...rest);
      };
      wrapped.level = true;
    }

    if (!wrapped.offer && P.LevelUp && typeof P.LevelUp.offer === 'function') {
      const origOffer = P.LevelUp.offer.bind(P.LevelUp);
      P.LevelUp.offer = function (...a) {
        const r = origOffer(...a);
        try { if (pendingCardOffer && !pendingCardOffer.done && Array.isArray(r)) { pendingCardOffer.options = r; pendingCardOffer.at = Date.now(); } } catch (_) {}
        return r;
      };
      wrapped.offer = true;
    }
    return true;
  }

  const PANEL_CSS = `
#plh-panel{--bg:rgba(18,21,31,.9);--card:rgba(255,255,255,.045);--line:rgba(255,255,255,.09);--txt:#e9edf7;--mut:#8f99b3;--acc:#6c8cff;--ok:#34d27b;--bad:#ff5468;--warn:#f5b83d;
 position:fixed;z-index:2147483647;right:14px;bottom:14px;display:flex;flex-direction:column;color:var(--txt);background:var(--bg);-webkit-backdrop-filter:blur(16px) saturate(1.3);backdrop-filter:blur(16px) saturate(1.3);
 border:1px solid var(--line);border-radius:18px;box-shadow:0 14px 44px rgba(0,0,0,.55),0 0 0 1px rgba(255,255,255,.03) inset;font:13px/1.4 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,system-ui,sans-serif;overflow:hidden;box-sizing:border-box}
#plh-panel *{box-sizing:border-box}
#plh-panel #plh-title{display:flex;align-items:center;gap:10px;padding:10px 12px;cursor:move;user-select:none;-webkit-user-select:none;touch-action:none;background:linear-gradient(135deg,rgba(108,140,255,.18),rgba(52,210,123,.08))}
#plh-panel .plh-logo{width:26px;height:26px;border-radius:9px;background:linear-gradient(135deg,#6c8cff,#a46bff);display:grid;place-items:center;font-size:14px;flex:none;box-shadow:0 2px 8px rgba(108,140,255,.45)}
#plh-panel .plh-name{flex:1;min-width:0;line-height:1.15}
#plh-panel .plh-name b{display:block;font-size:13.5px;font-weight:650;letter-spacing:.2px}
#plh-panel .plh-name small{color:var(--mut);font-size:10.5px;display:flex;align-items:center;gap:5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#plh-panel #plh-dot{width:8px;height:8px;border-radius:50%;background:var(--ok);display:inline-block;flex:none;box-shadow:0 0 8px currentColor;color:var(--ok)}
#plh-panel .plh-master{display:flex;align-items:center;gap:7px;font-weight:650;font-size:11.5px;letter-spacing:.4px;cursor:pointer;flex:none}
#plh-panel .plh-iconbtn{width:28px;height:28px;border-radius:9px;border:1px solid var(--line);background:var(--card);color:var(--txt);cursor:pointer;font-size:15px;line-height:1;display:grid;place-items:center;padding:0;flex:none;transition:.15s}
#plh-panel .plh-iconbtn:hover{background:rgba(255,255,255,.12)}
#plh-panel #plh-body{padding:10px 12px 12px;overflow:auto;-webkit-overflow-scrolling:touch;flex:1;min-height:0}
#plh-panel #plh-body::-webkit-scrollbar{width:6px}#plh-panel #plh-body::-webkit-scrollbar-thumb{background:rgba(255,255,255,.18);border-radius:6px}
#plh-panel .plh-card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:9px 10px;margin-bottom:9px}
#plh-panel .plh-hprow{display:flex;align-items:center;gap:8px;margin-bottom:7px}
#plh-panel .plh-hpbar{flex:1;height:7px;border-radius:7px;background:rgba(255,255,255,.1);overflow:hidden}
#plh-panel #plh-hpfill{height:100%;width:0;border-radius:7px;background:var(--ok);transition:width .25s,background .25s}
#plh-panel #plh-hptxt{font-size:11px;color:var(--mut);min-width:64px;text-align:right;font-variant-numeric:tabular-nums}
#plh-panel #plh-status{font-size:11.5px;color:#cfd6ea;word-break:break-word}
#plh-panel #plh-minimap{display:block;margin:8px auto 0;border-radius:10px;border:1px solid var(--line);background:#0c0f17}
#plh-panel details{background:var(--card);border:1px solid var(--line);border-radius:12px;margin-bottom:9px;overflow:hidden}
#plh-panel summary{list-style:none;cursor:pointer;padding:9px 11px;font-weight:600;font-size:12.5px;display:flex;align-items:center;justify-content:space-between;user-select:none}
#plh-panel summary::-webkit-details-marker{display:none}
#plh-panel summary::after{content:"›";color:var(--mut);font-size:16px;transition:transform .15s}
#plh-panel details[open]>summary::after{transform:rotate(90deg)}
#plh-panel .plh-sec{padding:0 11px 8px}
#plh-panel .plh-row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:6px 0;border-top:1px solid var(--line);cursor:pointer}
#plh-panel .plh-row:first-child{border-top:0}
#plh-panel .plh-row span{flex:1;min-width:0}
#plh-panel .plh-row small{display:block;color:var(--mut);font-size:10.5px}
#plh-panel input.plh-sw{appearance:none;-webkit-appearance:none;width:34px;height:20px;border-radius:20px;background:#3b4258;position:relative;cursor:pointer;transition:background .18s;flex:none;margin:0;outline:none}
#plh-panel input.plh-sw::after{content:"";position:absolute;top:2px;left:2px;width:16px;height:16px;border-radius:50%;background:#fff;transition:transform .18s;box-shadow:0 1px 3px rgba(0,0,0,.4)}
#plh-panel input.plh-sw:checked{background:var(--ok)}
#plh-panel input.plh-sw:checked::after{transform:translateX(14px)}
#plh-panel input.plh-sw.plh-big{width:42px;height:24px}
#plh-panel input.plh-sw.plh-big::after{width:20px;height:20px}
#plh-panel input.plh-sw.plh-big:checked::after{transform:translateX(18px)}
#plh-panel button.plh-btn{border:1px solid var(--line);background:var(--card);color:var(--txt);border-radius:10px;padding:7px 10px;font:inherit;font-size:12px;cursor:pointer;transition:.15s}
#plh-panel button.plh-btn:hover{background:rgba(255,255,255,.12)}
#plh-panel button.plh-btn.plh-pri{background:linear-gradient(135deg,#5b7cff,#8a5bff);border-color:transparent;font-weight:600}
#plh-panel button.plh-btn.plh-danger{color:#ff8d9b}
#plh-panel .plh-btnrow{display:flex;gap:6px;flex-wrap:wrap;margin-top:7px}
#plh-panel .plh-btnrow .plh-btn{flex:1;white-space:nowrap}
#plh-panel .plh-info{font-size:11px;color:var(--mut);margin-top:5px}
#plh-panel textarea{width:100%;background:rgba(0,0,0,.3);border:1px solid var(--line);border-radius:8px;color:var(--txt);padding:6px;font:11px/1.35 ui-monospace,Menlo,Consolas,monospace;resize:vertical}
#plh-panel input[type=range]{accent-color:var(--acc);width:100%}
#plh-panel .plh-foot{text-align:center;color:var(--mut);font-size:10.5px;padding-top:2px}
#plh-panel.plh-min{width:auto!important;min-width:0}
#plh-panel.plh-min .plh-name small{display:none}
@media (max-width:640px){#plh-panel{bottom:8px}}
#plh-dock{position:fixed;z-index:2147483647;right:12px;top:100px;display:flex;flex-direction:column;gap:10px;touch-action:none;user-select:none;-webkit-user-select:none}
#plh-dock button{width:46px;height:46px;border-radius:50%;border:1.5px solid rgba(255,255,255,.28);background:rgba(24,28,42,.84);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px);color:#c9d1e8;display:grid;place-items:center;padding:0;cursor:pointer;box-shadow:0 6px 18px rgba(0,0,0,.45);transition:transform .12s,background .2s,box-shadow .2s,color .2s,border-color .2s;-webkit-tap-highlight-color:transparent;touch-action:none;font:inherit}
#plh-dock button:active{transform:scale(.92)}
#plh-dock button svg{display:block;pointer-events:none}
#plh-dock #plh-btn-toggle.plh-on{background:linear-gradient(135deg,#1fbf75,#13a063);color:#fff;border-color:rgba(255,255,255,.55);box-shadow:0 0 0 3px rgba(52,210,123,.25),0 6px 18px rgba(0,0,0,.45)}
#plh-dock #plh-btn-toggle:not(.plh-on){color:#ff8d9b;border-color:rgba(255,84,104,.55)}
#plh-dock #plh-btn-menu.plh-open{background:linear-gradient(135deg,#5b7cff,#8a5bff);color:#fff;border-color:transparent}
#plh-panel .plh-perf{font-size:10.5px;color:var(--mut);margin-top:5px;font-variant-numeric:tabular-nums}
#plh-panel .plh-hist{display:flex;flex-direction:column;gap:5px;margin-top:7px}
#plh-panel .plh-hist-item{display:flex;align-items:center;gap:8px;padding:6px 8px;border:1px solid var(--line);border-radius:9px;background:rgba(0,0,0,.18);font-size:11px}
#plh-panel .plh-hist-item span{flex:1;min-width:0}
#plh-panel .plh-hist-item small{display:block;color:var(--mut);font-size:10px}
#plh-panel .plh-hist-item button{border:1px solid var(--line);background:var(--card);color:var(--txt);border-radius:8px;padding:4px 8px;font:inherit;font-size:11px;cursor:pointer}
`;
  const ICON_POWER = '<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3v8"/><path d="M6.4 6.9a8 8 0 1 0 11.2 0"/></svg>';
  const ICON_PANEL = '<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><rect x="4" y="4" width="16" height="16" rx="5"/><path d="M8.5 9.5h7M8.5 12.5h7M8.5 15.5h4"/></svg>';
  function setPanelHidden(v) {
    panelPrefs.hidden = !!v;
    try { localStorage.setItem('plh_panel_hidden', v ? '1' : '0'); } catch (_) {}
    const el = document.getElementById('plh-panel'); if (el) el.style.display = v ? 'none' : '';
    syncEnabledUI();
    if (!v) { try { W.dispatchEvent(new CustomEvent('plh-reports')); } catch (_) {} }
  }
  // v0.9.1: chỉ 2 biểu tượng nổi (mọi thiết bị): [bật/tắt bot] và [ẩn/hiện toàn bộ bảng]; kéo để đổi chỗ
  function buildDock() {
    if (document.getElementById('plh-dock')) return;
    const dock = document.createElement('div'); dock.id = 'plh-dock';
    const mkBtn = (id, title, icon) => { const b = document.createElement('button'); b.id = id; b.type = 'button'; b.title = title; b.setAttribute('aria-label', title); b.innerHTML = icon; return b; };
    const bPow = mkBtn('plh-btn-toggle', 'Bật / tắt bot', ICON_POWER), bPan = mkBtn('plh-btn-menu', 'Ẩn / hiện bảng điều khiển', ICON_PANEL);
    dock.append(bPow, bPan); document.documentElement.appendChild(dock);
    const place = (l, t) => { dock.style.left = clamp(l, 0, Math.max(0, innerWidth - 50)) + 'px'; dock.style.top = clamp(t, 0, Math.max(0, innerHeight - 110)) + 'px'; dock.style.right = 'auto'; };
    try { const pos = JSON.parse(localStorage.getItem('plh_dock_pos') || 'null'); if (pos && Number.isFinite(pos.left) && Number.isFinite(pos.top)) place(pos.left, pos.top); } catch (_) {}
    addEventListener('resize', () => { const r = dock.getBoundingClientRect(); if (dock.style.left) place(r.left, r.top); });
    let drag = null, moved = false;
    for (const b of [bPow, bPan]) {
      b.addEventListener('pointerdown', e => { const r = dock.getBoundingClientRect(); drag = { dx: e.clientX - r.left, dy: e.clientY - r.top, x0: e.clientX, y0: e.clientY }; moved = false; try { b.setPointerCapture(e.pointerId); } catch (_) {} });
      b.addEventListener('pointermove', e => { if (!drag) return; if (Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) > 7) moved = true; if (moved) place(e.clientX - drag.dx, e.clientY - drag.dy); });
      b.addEventListener('pointerup', () => { if (drag && moved) { try { const r = dock.getBoundingClientRect(); localStorage.setItem('plh_dock_pos', JSON.stringify({ left: r.left, top: r.top })); } catch (_) {} } drag = null; setTimeout(() => { moved = false; }, 0); });
      b.addEventListener('pointercancel', () => { drag = null; moved = false; });
    }
    bPow.addEventListener('click', () => { if (moved) return; state.enabled = !state.enabled; persistSettings(); syncEnabledUI(); });
    bPan.addEventListener('click', () => { if (moved) return; setPanelHidden(!panelPrefs.hidden); });
    syncEnabledUI();
  }

  function panel() {
    if (!document.documentElement || document.getElementById('plh-panel')) return;
    if (!document.getElementById('plh-style')) { const st = document.createElement('style'); st.id = 'plh-style'; st.textContent = PANEL_CSS; (document.head || document.documentElement).appendChild(st); }
    const el = document.createElement('div');
    el.id = 'plh-panel';
    const panelWidth = isIOS ? '270px' : '318px';
    el.style.cssText = `width:${panelWidth};max-height:${isIOS ? 'calc(100vh - 80px)' : '82vh'};right:70px;bottom:12px`;
    el.innerHTML = `<div id="plh-title">
        <div class="plh-logo">⚡</div>
        <div class="plh-name"><b>PokeLoop Bot</b><small><i id="plh-dot"></i><span id="plh-pill">v${VERSION}</span></small></div>
        <label class="plh-master" title="Bật/tắt bot (gồm cả tự chọn thẻ)"><span id="plh-mastertxt">BOT</span><input type="checkbox" class="plh-sw plh-big" data-state="enabled"></label>
        <button id="plh-min" type="button" class="plh-iconbtn" title="Ẩn bảng (bấm biểu tượng bên cạnh để hiện lại)">✕</button>
      </div>
      <div id="plh-body">
        <div class="plh-card">
          <div class="plh-hprow"><div class="plh-hpbar"><div id="plh-hpfill"></div></div><div id="plh-hptxt">—</div></div>
          <div id="plh-status">Đang khởi tạo…</div>
          <div id="plh-perf" class="plh-perf"></div>
        </div>
        <div id="plh-controls"></div>
        <div class="plh-foot">${isIOS ? 'Giữ màn hình sáng khi chơi' : 'F8 bật/tắt bot · F9 ẩn/hiện bảng · kéo 2 nút để di chuyển'}</div>
      </div>`;
    document.documentElement.appendChild(el);

    const master = el.querySelector('input[data-state="enabled"]');
    master.checked = !!state.enabled;
    master.addEventListener('change', () => { state.enabled = master.checked; persistSettings(); syncEnabledUI(); });

    buildDock(el);

    try {
      const pos = JSON.parse(localStorage.getItem('plh_panel_pos') || 'null');
      if (pos && Number.isFinite(pos.left) && Number.isFinite(pos.top)) {
        el.style.left = clamp(pos.left, 0, innerWidth - el.offsetWidth) + 'px';
        el.style.top = clamp(pos.top, 0, innerHeight - el.offsetHeight) + 'px';
        el.style.right = 'auto'; el.style.bottom = 'auto';
      }
    } catch (_) {}

    const title = el.querySelector('#plh-title');
    title.addEventListener('pointerdown', e => {
      if (e.target.closest('button,label,input')) return;
      const r = el.getBoundingClientRect();
      panelDrag = { dx: e.clientX - r.left, dy: e.clientY - r.top };
      title.setPointerCapture(e.pointerId);
    });
    title.addEventListener('pointermove', e => {
      if (!panelDrag) return;
      el.style.left = clamp(e.clientX - panelDrag.dx, 0, innerWidth - el.offsetWidth) + 'px';
      el.style.top = clamp(e.clientY - panelDrag.dy, 0, innerHeight - el.offsetHeight) + 'px';
      el.style.right = 'auto'; el.style.bottom = 'auto';
    });
    title.addEventListener('pointerup', () => {
      if (!panelDrag) return; panelDrag = null;
      try { const r = el.getBoundingClientRect(); localStorage.setItem('plh_panel_pos', JSON.stringify({ left: r.left, top: r.top })); } catch (_) {}
    });

    el.querySelector('#plh-min').addEventListener('click', () => setPanelHidden(true));
    el.style.display = panelPrefs.hidden ? 'none' : '';

    // ----- các nhóm điều khiển -----
    const box = el.querySelector('#plh-controls');
    const LITE_HIDE = ['Học từ bạn', '📊 Báo cáo ván'];
    const group = (title, open) => { const d = document.createElement('details'); if (LITE_HIDE.includes(title)) d.style.display = 'none'; if (open) d.open = true; const sm = document.createElement('summary'); sm.textContent = title; const sec = document.createElement('div'); sec.className = 'plh-sec'; d.append(sm, sec); box.appendChild(d); return sec; };
    const addCheck = (sec, key, label, hint, onChange) => {
      const l = document.createElement('label'); l.className = 'plh-row';
      const sp = document.createElement('span'); sp.textContent = label; if (hint) { const sm = document.createElement('small'); sm.textContent = hint; sp.appendChild(sm); }
      const c = document.createElement('input'); c.type = 'checkbox'; c.className = 'plh-sw'; c.checked = !!state[key]; c.dataset.state = key;
      c.addEventListener('change', () => { state[key] = c.checked; persistSettings(); if (onChange) onChange(c.checked); });
      l.append(sp, c); sec.appendChild(l);
    };
    const addBtn = (parent, text, fn, cls) => { const b = document.createElement('button'); b.type = 'button'; b.className = 'plh-btn ' + (cls || ''); b.textContent = text; b.onclick = fn; parent.appendChild(b); return b; };

    const g1 = group('Chức năng bot', true);
    addCheck(g1, 'dodge', 'Né đòn'); addCheck(g1, 'loot', 'Nhặt đồ rơi (XP, tiền, táo…)'); addCheck(g1, 'chest', 'Mở rương'); addCheck(g1, 'buff', 'Cột buff / suối / bàn thờ');
    addCheck(g1, 'events', 'Sự kiện nhỏ', 'Meowth, giải cứu Pokémon lạc'); addCheck(g1, 'bigEvent', 'Sự kiện lớn', 'Halloween: nhặt bí ngô, kẹo…');
    addCheck(g1, 'autoRift', 'Tự vào rift'); addCheck(g1, 'relocate', 'Đổi chỗ khi bị vây (relocate)');

    const gS = group('Chế độ đặc biệt', true);
    addCheck(gS, 'coop', 'Co-op', 'Bám đội hình, đi hồi sinh đồng đội, né rộng hơn khi là khách');
    addCheck(gS, 'ticketFocus', 'Ưu tiên vé', 'Nhặt vé trước, đuổi lâu hơn con mang vé ×10');
    addCheck(gS, 'titanMode', 'Titan Rift', 'Chạy vào vòng an toàn khi NOVA, diệt bản sao, giữ vòng quanh Titan');
    addCheck(gS, 'judgeMode', 'Boss phán xét (phút 30)', 'Giữ xa Arceus bất tử, hạ huyền thoại được gọi ra');
    addCheck(gS, 'yieldInput', 'Nhường khi bạn bấm phím', 'Phím / tay cầm thật của bạn ghi đè bot 0,9 giây rồi bot tự chạy lại');

    const gK = group('Cửa hàng Kecleon', false);
    addCheck(gK, 'shopBuy', 'Tự mua đồ ở Kecleon', 'Chỉ đi tới khi trong 3 món có món bạn tick bên dưới; không có thì bỏ qua, không mua món khác');
    const shopNote = document.createElement('div'); shopNote.style.cssText = 'font-size:11px;opacity:.7;padding:2px 0 4px'; shopNote.textContent = 'Tick món muốn mua (ưu tiên từ trên xuống). Mỗi ván chỉ mua được 1 món.'; gK.appendChild(shopNote);
    for (const id of SHOP_ORDER) {
      const l = document.createElement('label'); l.style.cssText = 'display:flex;align-items:center;gap:6px;padding:2px 0;font-size:12px';
      const c = document.createElement('input'); c.type = 'checkbox'; c.checked = state.shopWant.includes(id);
      c.addEventListener('change', () => { state.shopWant = SHOP_ORDER.filter(x => x === id ? c.checked : state.shopWant.includes(x)); persistSettings(); });
      const sp = document.createElement('span'); sp.textContent = `${SHOP_NAME[id]} — ${SHOP_PRICE[id]}`;
      l.append(c, sp); gK.appendChild(l);
    }

    const gC = group('Chọn thẻ lên cấp', false);
    addCheck(gC, 'cardPick', 'Chọn thẻ theo danh sách của tôi', 'Thẻ bạn tick được chọn trước (trên → dưới = ưu tiên). Lượt nào không có thẻ tick thì bot chấm điểm như cũ');
    addCheck(gC, 'cardReroll', 'Không có thẻ đã tick thì đổi thẻ (reroll)', 'Đổi tối đa 1 lần mỗi lượt lên cấp, nếu game còn lượt đổi');
    const cardTitle = t => { const d = document.createElement('div'); d.style.cssText = 'font-weight:650;font-size:12px;padding:9px 0 3px'; d.textContent = t; gC.appendChild(d); return d; };
    const cardScroll = () => { const b = document.createElement('div'); b.style.cssText = 'max-height:190px;overflow-y:auto;-webkit-overflow-scrolling:touch;overscroll-behavior:contain;border:1px solid var(--line);border-radius:9px;padding:3px 8px;background:var(--card)'; gC.appendChild(b); return b; };
    const cardRow = (box, checked, label, sub, title, onChange) => {
      const l = document.createElement('label'); l.style.cssText = 'display:flex;align-items:center;gap:7px;padding:4px 0;font-size:12px;border-top:1px solid var(--line)';
      const c = document.createElement('input'); c.type = 'checkbox'; c.checked = checked; c.addEventListener('change', () => onChange(c.checked));
      const sp = document.createElement('span'); sp.style.cssText = 'flex:1;min-width:0'; sp.textContent = label; if (title) sp.title = title;
      if (sub) { const sm = document.createElement('small'); sm.style.cssText = 'display:block;opacity:.6;font-size:10.5px'; sm.textContent = sub; sp.appendChild(sm); }
      l.append(c, sp); box.appendChild(l); return c;
    };
    // ① chiêu thức theo nhân vật
    cardTitle('① Chiêu thức của nhân vật');
    const monBar = document.createElement('div'); monBar.style.cssText = 'display:flex;gap:6px;padding:0 0 5px'; gC.appendChild(monBar);
    const monSearch = document.createElement('input'); monSearch.type = 'search'; monSearch.placeholder = 'Tìm Pokémon…'; monSearch.style.cssText = 'flex:1;min-width:0;padding:6px 8px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--txt);font-size:12px';
    const monSel = document.createElement('select'); monSel.style.cssText = 'flex:1.3;min-width:0;padding:6px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--txt);font-size:12px';
    monBar.append(monSearch, monSel);
    const monInfo = document.createElement('div'); monInfo.style.cssText = 'font-size:11px;opacity:.7;padding:0 0 4px'; gC.appendChild(monInfo);
    const movesBox = cardScroll();
    const moveBtns = document.createElement('div'); moveBtns.style.cssText = 'display:flex;gap:8px;padding:6px 0 0'; gC.appendChild(moveBtns);
    let shownDex = -1, shownAuto = '';
    const selMon = () => state.cardMon ? monByNum(state.cardMon) : currentMon();
    const fillMonSel = () => {
      const q = monSearch.value.trim().toLowerCase(), cur = currentMon();
      monSel.innerHTML = '';
      const o0 = document.createElement('option'); o0.value = ''; o0.textContent = 'Tự nhận diện' + (cur ? `: #${cur.dex} ${cur.name}` : ' (chưa vào ván)'); monSel.appendChild(o0);
      let n = 0; for (const m of allMons()) { if (q && !(String(m.name).toLowerCase().includes(q) || String(m.dex) === q)) continue; if (n++ > 3000) break; const o = document.createElement('option'); o.value = String(m.dex); o.textContent = `#${m.dex} ${m.name}`; monSel.appendChild(o); }
      if (state.cardMon && !Array.from(monSel.options).some(o => o.value === String(state.cardMon))) { const m = monByNum(state.cardMon); if (m) { const o = document.createElement('option'); o.value = String(m.dex); o.textContent = `#${m.dex} ${m.name}`; monSel.appendChild(o); } }
      monSel.value = String(state.cardMon || '');
    };
    const renderMoves = () => {
      const mon = selMon(); movesBox.innerHTML = ''; shownDex = mon ? mon.dex : 0;
      const M = safe(() => W.__PL.Moves, null);
      if (!mon || !M) { monInfo.textContent = mon ? 'Đang nạp dữ liệu game…' : 'Vào ván một lần để bot nhận diện nhân vật, hoặc chọn Pokémon ở ô bên trên.'; return; }
      const reg = movesOfMon(mon), spec = specialsOfMon(mon), ids = [...reg, ...spec.map(x => x.id)], have = () => (Array.isArray(state.cardMoves[mon.dex]) ? state.cardMoves[mon.dex] : []);
      monInfo.textContent = `${mon.name} (#${mon.dex}) · hệ ${(mon.types || []).join('/')} · ${reg.length} chiêu thường + ${spec.length} chiêu đặc biệt · ưu tiên từ trên xuống`;
      const rowFor = (id, label) => {
        const mv = M.BY_ID[id];
        cardRow(movesBox, have().includes(id), (label ? label + ' · ' : '') + (mv.name || id), [mv.type, mv.kind].filter(Boolean).join(' · '), mv.desc || '', on => { state.cardMoves[mon.dex] = ids.filter(x => x === id ? on : have().includes(x)); persistSettings(); });
      };
      for (const id of reg) rowFor(id, '');
      if (spec.length) { const h = document.createElement('div'); h.textContent = '— Chiêu đặc biệt (độc quyền / Mega / Shiny) —'; h.style.cssText = 'font-size:11px;opacity:.75;padding:6px 4px 2px;border-top:1px solid var(--line);margin-top:4px'; movesBox.appendChild(h); for (const x of spec) rowFor(x.id, x.label); }
      if (!ids.length) monInfo.textContent += ' — (không đọc được danh sách chiêu)';
    };
    monSearch.addEventListener('input', fillMonSel);
    monSel.addEventListener('change', () => { state.cardMon = monSel.value; persistSettings(); renderMoves(); });
    addBtn(moveBtns, 'Tick hết chiêu (cả đặc biệt)', () => { const mon = selMon(); if (!mon) return; state.cardMoves[mon.dex] = allMovesOfMon(mon); persistSettings(); renderMoves(); });
    addBtn(moveBtns, 'Bỏ tick hết', () => { const mon = selMon(); if (!mon) return; state.cardMoves[mon.dex] = []; persistSettings(); renderMoves(); });
    // ② thẻ chỉ số
    cardTitle('② Thẻ chỉ số (tốc độ, hồi máu…)');
    const statBox = cardScroll();
    for (const id of STAT_ORDER) {
      const st = safe(() => W.__PL.LevelUp.STATS.find(x => x.id === id), null);
      cardRow(statBox, state.cardStats.includes(id), STAT_LABEL[id], '', st ? `${st.title}: ${st.desc}` : '', on => { state.cardStats = STAT_ORDER.filter(x => x === id ? on : state.cardStats.includes(x)); persistSettings(); });
    }
    const statBtns = document.createElement('div'); statBtns.style.cssText = 'display:flex;gap:8px;padding:6px 0 0'; gC.appendChild(statBtns);
    addBtn(statBtns, 'Tick hết thẻ chỉ số', () => { state.cardStats = [...STAT_ORDER]; persistSettings(); statBox.querySelectorAll('input').forEach(c => { c.checked = true; }); });
    addBtn(statBtns, 'Bỏ tick hết', () => { state.cardStats = []; persistSettings(); statBox.querySelectorAll('input').forEach(c => { c.checked = false; }); });
    fillMonSel(); renderMoves();
    setInterval(() => {
      try {
        const mon = selMon(), dex = mon ? mon.dex : 0, cur = currentMon(), autoLbl = cur ? cur.dex : 0;
        if (dex !== shownDex || (!movesBox.children.length && mon)) renderMoves();
        if (autoLbl !== shownAuto && !monSearch.value) { shownAuto = autoLbl; fillMonSel(); }
      } catch (_) {}
    }, 2000);

    const gI = group('Item cầm tay', false);
    addCheck(gI, 'itemPick', 'Chọn item theo danh sách', 'Chỉ đi nhặt món bạn tick; ở màn "An item!" tự đổi/giữ/bỏ qua. Không tick món nào = bỏ qua mọi item');
    addCheck(gI, 'itemLock', 'Khóa khi đã cầm món ưu tiên cao nhất', 'Không bị hỏi nữa, item rơi sau đó nằm yên');
    const itemNote = document.createElement('div'); itemNote.style.cssText = 'font-size:11px;opacity:.7;padding:2px 0 4px'; itemNote.textContent = 'Tick các món muốn giữ (ưu tiên từ trên xuống). Chạm giữ tên món để xem mô tả.';
    gI.appendChild(itemNote);
    const itemChecks = [];
    for (const id of SHOP_ORDER) {
      const l = document.createElement('label'); l.style.cssText = 'display:flex;align-items:center;gap:6px;padding:2px 0;font-size:12px';
      const c = document.createElement('input'); c.type = 'checkbox'; c.checked = state.itemWant.includes(id); itemChecks.push([id, c]);
      c.addEventListener('change', () => { state.itemWant = SHOP_ORDER.filter(x => x === id ? c.checked : state.itemWant.includes(x)); persistSettings(); });
      const sp = document.createElement('span'); sp.textContent = SHOP_NAME[id]; sp.title = safe(() => W.__PL.Items.BY[id].desc, '') || '';
      l.append(c, sp); gI.appendChild(l);
    }
    const itemBtns = document.createElement('div'); itemBtns.style.cssText = 'display:flex;gap:8px;padding:6px 0 2px'; gI.appendChild(itemBtns);
    addBtn(itemBtns, 'Chọn tất cả', () => { state.itemWant = [...SHOP_ORDER]; itemChecks.forEach(([, c]) => { c.checked = true; }); persistSettings(); });
    addBtn(itemBtns, 'Bỏ chọn hết', () => { state.itemWant = []; itemChecks.forEach(([, c]) => { c.checked = false; }); persistSettings(); });

    // v0.9.20: Tự roll gacha — bấm đúng các nút của game (pull-100 vé vàng ×100, pull-10b vé tím ×10, rồi lẻ ×10/×1) cho tới hết vé. Không sửa vé, không đổi cài đặt game.
    const gG = group('Gacha tự động', false);
    const gx = { on: false, clicks: 0, msg: 'Mở màn Gacha, chọn banner rồi bấm Bắt đầu.' };
    const gsleep = ms => new Promise(r => setTimeout(r, ms));
    const gel = id => document.getElementById(id);
    const gvis = el => { if (!el || el.classList.contains('hidden')) return false; const cs = getComputedStyle(el); return cs.display !== 'none' && cs.visibility !== 'hidden' && el.getClientRects().length > 0; };
    const gTickets = () => {
      const tk = safe(() => W.__PL.DB.save.tickets, null);
      if (tk && Number.isFinite(Number(tk.t1))) return { t1: Number(tk.t1) || 0, t10: Number(tk.t10) || 0 };
      const m = String(gel('gacha-tickets')?.textContent || '').match(/(\d[\d.,]*)\D+(\d[\d.,]*)/);
      return m ? { t1: parseInt(m[1].replace(/\D/g, ''), 10) || 0, t10: parseInt(m[2].replace(/\D/g, ''), 10) || 0 } : null;
    };
    const gPick = tk => {
      if (tk.t1 >= 100 && gel('pull-100')) return 'pull-100';
      if (tk.t10 >= 1 && gel('pull-10b')) return 'pull-10b';
      if (tk.t1 >= 10 && gel('pull-10')) return 'pull-10';
      if (tk.t1 >= 1 && gel('pull-1')) return 'pull-1';
      return null;
    };
    const gSet = m => { gx.msg = m; if (gInfo) gInfo.textContent = m; };
    const gStop = m => { gx.on = false; gSet(m); gBtn.textContent = '▶ Bắt đầu roll'; gBtn.classList.add('plh-pri'); };
    async function gLoop() {
      gx.clicks = 0; let sigPrev = '', sigAt = Date.now(), noChange = 0;
      while (gx.on) {
        if (!gvis(gel('scr-gacha'))) return gStop(`Đã dừng: không còn ở màn Gacha (đã bấm ${gx.clicks} lần)`);
        const fx = gel('pull-fx');
        if (gvis(fx)) {   // đang có hiệu ứng / bảng kết quả: bấm Skip của game, lật các thẻ úp, rồi bấm "Tiếp tục"
          const close = gel('pull-close');
          if (gvis(close)) { close.click(); await gsleep(500); sigPrev = ''; continue; }
          const flip = [...document.querySelectorAll('button, [role="button"], .btn')].find(b => gvis(b) && /flip\s*all|lật\s*(hết|tất\s*cả)/i.test(b.textContent || ''));   // nút "Flip all" của game
          if (flip) { flip.click(); await gsleep(350); }
          const sk = [...fx.querySelectorAll('.summon-skip')].find(gvis); if (sk) sk.click();
          const down = [...fx.querySelectorAll('.pcard.down')]; for (const c of down) { if (!gx.on) return; c.click(); await gsleep(40); }
          const sig = down.length + '|' + fx.querySelectorAll('.pcard').length + '|' + !!sk + '|' + !!flip;
          if (sig !== sigPrev) { sigPrev = sig; sigAt = Date.now(); } else if (Date.now() - sigAt > 25000) return gStop('Đã dừng: bảng kết quả đứng yên 25s. Nút đang hiện: ' + ([...document.querySelectorAll('button')].filter(gvis).map(b => (b.textContent || '').trim().replace(/\s+/g, ' ')).filter(Boolean).slice(0, 10).join(' | ') || '(không thấy nút)') + ' — gửi tôi dòng này');
          await gsleep(250); continue;
        }
        sigPrev = ''; sigAt = Date.now();
        const tk = gTickets(); if (!tk) return gStop('Đã dừng: không đọc được số vé');
        const id = gPick(tk);
        if (!id) return gStop(`Hết vé — xong (đã bấm ${gx.clicks} lần)`);
        const btn = gel(id); if (!btn || btn.disabled) return gStop(`Đã dừng: nút ${id} không bấm được`);
        gSet(`Đang roll… ${id} · còn vé ×1: ${tk.t1}, vé ×10: ${tk.t10} · đã bấm ${gx.clicks}`);
        btn.click(); gx.clicks++;
        await gsleep(900);
        if (!gvis(gel('pull-fx'))) {   // không thấy bảng kết quả: kiểm tra vé có trừ không, nếu 2 lần liền không đổi thì dừng
          const tk2 = gTickets();
          if (tk2 && tk2.t1 === tk.t1 && tk2.t10 === tk.t10) { if (++noChange >= 2) return gStop('Đã dừng: bấm roll nhưng vé không đổi (có hộp thoại lạ?) — hãy xem màn hình'); } else noChange = 0;
        } else noChange = 0;
      }
    }
    const gRow = document.createElement('div'); gRow.className = 'plh-btnrow'; gG.appendChild(gRow);
    const gBtn = addBtn(gRow, '▶ Bắt đầu roll', () => { if (gx.on) { gStop(`Đã dừng (đã bấm ${gx.clicks} lần)`); return; } if (!gvis(gel('scr-gacha'))) { gSet('Hãy mở màn Gacha và chọn banner trước.'); return; } gx.on = true; gBtn.textContent = '⏹ Dừng'; gBtn.classList.remove('plh-pri'); gLoop(); });
    gBtn.classList.add('plh-pri');
    const gInfo = document.createElement('div'); gInfo.className = 'plh-info'; gInfo.textContent = gx.msg; gG.appendChild(gInfo);
    const gNote = document.createElement('div'); gNote.className = 'plh-info'; gNote.textContent = 'Thứ tự: vé vàng ×100 → vé tím ×10 → vé vàng lẻ ×10 rồi ×1, tới hết vé. Roll vào banner đang chọn. Bật "Skip animation" của game để nhanh hơn.'; gG.appendChild(gNote);
    const g2 = group('Học từ bạn', false);
    addCheck(g2, 'learnRec', 'Ghi lại khi tôi tự chơi', 'Chỉ ghi khi Bot đang tắt'); addCheck(g2, 'learnUse', 'Bot học theo cách tôi chơi');
    const lmWrap = document.createElement('div'); lmWrap.style.cssText = 'padding:6px 0 2px';
    const lmv = document.createElement('b'); lmv.textContent = `${Math.round((state.learnMix ?? 0.5) * 100)}%`;
    const lmr = document.createElement('input'); lmr.type = 'range'; lmr.min = '0'; lmr.max = '100'; lmr.step = '10'; lmr.value = String(Math.round((state.learnMix ?? 0.5) * 100));
    lmr.addEventListener('input', () => { state.learnMix = Number(lmr.value) / 100; lmv.textContent = `${lmr.value}%`; persistSettings(); });
    const lmt = document.createElement('div'); lmt.style.cssText = 'display:flex;justify-content:space-between;font-size:11.5px;color:var(--mut)'; lmt.append(document.createTextNode('Mức bắt chước'), lmv);
    lmWrap.append(lmt, lmr); g2.appendChild(lmWrap);
    const linfo = document.createElement('div'); linfo.id = 'plh-learn-info'; linfo.className = 'plh-info'; g2.appendChild(linfo);
    const upd = () => { const cardN = Object.keys(learn.cards).length; linfo.textContent = `${learn.ready ? '' : '(đang nạp…) '}Đã ghi ${learn.total} mẫu (≈${Math.round(learn.total * 0.15 / 60)} phút tự chơi) · ${cardN ? cardN + ' nhóm thẻ' : 'chưa có thẻ'} · theo giai đoạn: ${learn.seen.join('/')}`; };
    upd(); setInterval(upd, 2000);
    const lrow = document.createElement('div'); lrow.className = 'plh-btnrow'; g2.appendChild(lrow);
    addBtn(lrow, '💾 Sao lưu', () => exportLearn());
    const fin = document.createElement('input'); fin.type = 'file'; fin.accept = '.json,application/json'; fin.style.display = 'none';
    fin.onchange = async () => { const fl = fin.files && fin.files[0]; if (!fl) return; try { const n = await importLearn(fl); linfo.textContent = `Đã nạp thêm ${n} mẫu`; } catch (e) { linfo.textContent = 'Nạp lỗi: ' + e.message; } fin.value = ''; };
    lrow.appendChild(fin); addBtn(lrow, '📂 Nạp lại', () => fin.click());
    const lclr = addBtn(lrow, '🗑 Xoá', () => { if (lclr.dataset.c !== '1') { lclr.dataset.c = '1'; lclr.textContent = 'Bấm lần nữa'; setTimeout(() => { lclr.dataset.c = ''; lclr.textContent = '🗑 Xoá'; }, 3000); return; } clearLearn(); lclr.dataset.c = ''; lclr.textContent = '🗑 Xoá'; upd(); }, 'plh-danger');

    const g3 = group('Chọn thẻ & nâng cao', false);
    const pr = document.createElement('div'); pr.style.cssText = 'padding:4px 0 6px';
    const prl = document.createElement('div'); prl.style.cssText = 'font-size:11.5px;color:var(--mut);margin-bottom:4px'; prl.textContent = 'Thứ tự ưu tiên chỉ số (dấu phẩy)';
    const pri = document.createElement('textarea'); pri.rows = 2; pri.value = (state.priorities || []).join(', ');
    pri.addEventListener('change', () => { state.priorities = pri.value.split(',').map(x => x.trim().toLowerCase()).filter(Boolean); persistSettings(); });
    pr.append(prl, pri); g3.appendChild(pr);
    addCheck(g3, 'reroll', 'Đổi thẻ khi thẻ kém', '(<150 điểm; chỉ khi Bot đang bật)'); addCheck(g3, 'autoRestart', 'Tự chơi lại khi thua');
    if (!isIOS) { addCheck(g3, 'background', 'Chạy nền', 'Bật "Keep playing in the background" của game + giữ game chạy khi chuyển tab'); addCheck(g3, 'bgAudio', 'Chống giảm tốc tab ẩn', 'Phát âm thanh gần như im lặng khi tab ẩn'); }

    const gH = group('🧰 Mở hòm toàn map', true);
    addCheck(gH, 'chestHunt', 'Quét & mở hòm toàn map', 'Không xét máu / số quái; nhớ mọi hòm đã thấy, đi tới mở từng hòm');
    addCheck(gH, 'chestForce', 'Mở hòm bất chấp', 'Có hòm (hoặc đang tìm hòm) là đi thẳng tới mở: KHÔNG né quái, né đòn, né vùng, bất kể máu. Chỉ vòng qua tường. Dễ chết hơn, tắt = bot chơi bình thường');
    addCheck(gH, 'chestExplore', 'Thám hiểm khi chưa biết hòm nào', 'Chỉ khi quanh đây vắng quái');
    const crWrap = document.createElement('div'); crWrap.style.cssText = 'padding:6px 0 2px';
    const crv = document.createElement('b'); crv.textContent = `${state.chestRange}px`;
    const crr = document.createElement('input'); crr.type = 'range'; crr.min = '1500'; crr.max = '8000'; crr.step = '500'; crr.value = String(state.chestRange);
    crr.addEventListener('input', () => { state.chestRange = Number(crr.value); crv.textContent = `${crr.value}px`; persistSettings(); });
    const crt = document.createElement('div'); crt.style.cssText = 'display:flex;justify-content:space-between;font-size:11.5px;color:var(--mut)'; crt.append(document.createTextNode('Phạm vi tìm hòm'), crv);
    crWrap.append(crt, crr); gH.appendChild(crWrap);
    const hinfo = document.createElement('div'); hinfo.id = 'plh-hunt-info'; hinfo.className = 'plh-info'; gH.appendChild(hinfo);

    const gR = group('📊 Báo cáo ván', false);
    addCheck(gR, 'autoDownload', 'Tự tải khi hết ván', 'Chỉ tải khi cả ván kết thúc (không tải sau rift); mọi ván ≥10s đều được lưu trong lịch sử', v => runLog.setAutoDownload(v));
    const rrow = document.createElement('div'); rrow.className = 'plh-btnrow'; gR.appendChild(rrow);
    addBtn(rrow, '⬇ Tải ván gần nhất', () => runLog.exportLatest(), 'plh-pri'); addBtn(rrow, '📈 So sánh 10 ván', () => runLog.compare());
    const hist = document.createElement('div'); hist.className = 'plh-hist'; gR.appendChild(hist);
    const fmtDur = s => `${String(Math.floor(s / 60)).padStart(2, '0')}:${String(Math.floor(s % 60)).padStart(2, '0')}`;
    const refreshHist = async () => {
      try {
        const list = await runLog.listReports(); hist.textContent = '';
        if (!list.length) { const e = document.createElement('div'); e.className = 'plh-info'; e.textContent = 'Chưa có ván nào được lưu.'; hist.appendChild(e); return; }
        for (const r of list.slice(0, 8)) {
          const it = document.createElement('div'); it.className = 'plh-hist-item';
          const sp = document.createElement('span'); sp.textContent = `${new Date(r.startedAt).toLocaleTimeString()} · ${fmtDur(r.dur || 0)} · Lv ${r.level ?? '?'}`;
          const sm = document.createElement('small'); sm.textContent = `${r.kills ?? 0} quái · ${r.reason || ''}`; sp.appendChild(sm);
          const bt = document.createElement('button'); bt.type = 'button'; bt.textContent = '⬇'; bt.onclick = () => runLog.downloadById(r.id);
          it.append(sp, bt); hist.appendChild(it);
        }
      } catch (_) {}
    };
    W.addEventListener('plh-reports', refreshHist); refreshHist();
    setInterval(() => { const h = document.getElementById('plh-hunt-info'); if (h) h.textContent = `Đã biết ${chestMem.size} hòm · đang còn ${huntStats.active} · đã mở ${huntStats.opened} · quét ${huntStats.scanned || 0} ô (${huntStats.queue ? 'còn ' + huntStats.queue : 'xong'}, ${perf.wideMs.toFixed(1)}ms)`; }, 1500);
    const spacer = document.createElement('div'); spacer.style.height = '8px'; box.appendChild(spacer);
    syncEnabledUI();
  }

  // đồng bộ mọi nơi hiển thị trạng thái bật/tắt bot (công tắc, nút nổi iPhone, chấm màu)
  function syncEnabledUI() {
    try {
      document.querySelectorAll('input[data-state="enabled"]').forEach(c => { c.checked = !!state.enabled; });
      const t = document.getElementById('plh-btn-toggle'); if (t) t.classList.toggle('plh-on', !!state.enabled);
      const mb = document.getElementById('plh-btn-menu'); if (mb) mb.classList.toggle('plh-open', !panelPrefs.hidden);
      const mt = document.getElementById('plh-mastertxt'); if (mt) { mt.textContent = state.enabled ? 'BOT BẬT' : 'BOT TẮT'; mt.style.color = state.enabled ? 'var(--ok)' : 'var(--mut)'; }
      const dot = document.getElementById('plh-dot'); if (dot) { dot.style.background = state.enabled ? '#34d27b' : '#ff5468'; dot.style.color = state.enabled ? '#34d27b' : '#ff5468'; }
    } catch (_) {}
  }

  function drawMinimap(P) {
    try {
      const host = document.getElementById('plh-status'); if (!host) return;
      let cv = document.getElementById('plh-minimap');
      if (!cv) { cv = document.createElement('canvas'); cv.id = 'plh-minimap'; cv.width = 150; cv.height = 150; cv.style.cssText = 'display:block;margin:4px auto;background:#0e1118;border:1px solid #3a4256;border-radius:4px'; host.after(cv); }
      const g = cv.getContext('2d'), p = P.Game.player; if (!p) return;
      const S = 150 / 3000, cx = 75, cy = 75, to = (x, y) => [cx + (x - p.x) * S, cy + (y - p.y) * S];
      g.clearRect(0, 0, 150, 150);
      const col = { bigchest: '#ffd34d', chest: '#c8963c', altar: '#b07cff', spring: '#5ee0a0', trap: '#ff4d4d' };
      for (const m of mapMem.values()) { if (m.sp.dead || m.sp.used) continue; const [x, y] = to(m.x, m.y); g.fillStyle = col[m.type] || '#888'; g.fillRect(x - 2, y - 2, 4, 4); }
      for (const q of safe(() => P.Pickups.all(), []) || []) { const [x, y] = to(q.x, q.y); g.fillStyle = /xp/i.test(q.kind) ? '#4fc3ff' : '#fff'; g.fillRect(x, y, 1.5, 1.5); }
      for (const e of safe(() => P.EnemyMgr.all(), []) || []) { const [x, y] = to(e.x, e.y); g.fillStyle = e.boss ? '#ff00ff' : '#ff6b6b'; g.fillRect(x, y, 2, 2); }
      const rp = safe(() => P.Rift.rift, null); if (rp) { const [x, y] = to(rp.x, rp.y); g.strokeStyle = '#a06bff'; g.beginPath(); g.arc(x, y, 4, 0, 7); g.stroke(); }
      if (goalState.goal) { const [x, y] = to(goalState.goal.x, goalState.goal.y); g.strokeStyle = '#46e36f'; g.beginPath(); g.moveTo(cx, cy); g.lineTo(x, y); g.stroke(); }
      g.fillStyle = '#46e36f'; g.beginPath(); g.arc(cx, cy, 3, 0, 7); g.fill();
    } catch (_) {}
  }

  function setBootStatus(message, isError = false) {
    try {
      let box = document.getElementById('plh-boot-status');
      if (!box && document.documentElement) {
        box = document.createElement('div'); box.id = 'plh-boot-status';
        box.style.cssText = 'position:fixed;z-index:2147483647;left:12px;bottom:12px;background:#171923;color:#fff;padding:8px 11px;border:1px solid #65708a;border-radius:7px;font:12px sans-serif;max-width:320px;word-break:break-all';
        document.documentElement.appendChild(box);
      }
      if (box) { box.textContent = message; box.style.color = isError ? '#ff5b5b' : '#fff'; box.style.borderColor = isError ? '#ff3333' : '#65708a'; }
    } catch (_) {}
  }

  document.addEventListener('keydown', e => {
    if (e.key === 'F8') {
      state.enabled = !state.enabled; persistSettings(); syncEnabledUI();
    }
    if (e.key === 'F9') setPanelHidden(!panelPrefs.hidden);
  });

  // v0.9.10: Chọn item cầm tay. Màn "An item!" (chỉ cầm được 1 món): đổi/giữ/khóa theo danh sách tick (thứ tự trên → dưới = ưu tiên).
  let itemSeenAt = 0, itemActAt = 0;
  const itemRank = id => (id && (!state.itemPick || state.itemWant.includes(id))) ? SHOP_ORDER.indexOf(id) : Infinity;   // v0.9.12: không bật 'Chọn item' = coi mọi món đều được (xếp theo thứ tự mặc định)
  const itemIdFromText = (P, txt) => { let best = null, len = 0; for (const id of SHOP_ORDER) { const nm = safe(() => P.Items.BY[id].name, '') || SHOP_NAME[id]; if (nm && txt.includes(nm) && nm.length > len) { best = id; len = nm.length; } } return best; };
  const iconSrcCache = {};
  const itemIdFromCard = (P, card) => {
    const img = card.querySelector('img'), src = img && img.getAttribute('src');
    if (src) for (const id of SHOP_ORDER) {
      if (!(id in iconSrcCache)) { const t = document.createElement('template'); t.innerHTML = String(safe(() => P.Icons.html(id, 44), '')); iconSrcCache[id] = t.content.querySelector('img')?.getAttribute('src') || null; }
      if (iconSrcCache[id] && iconSrcCache[id] === src) return id;
    }
    return itemIdFromText(P, card.textContent || '');
  };
  setInterval(() => {
    try {
      if (!state.enabled) { itemSeenAt = 0; return; }   // v0.9.12: luôn tự xử lý màn 'An item!' khi bot bật — nếu không game đứng ở trạng thái 'choice' mãi (bot kẹt sau khi mở hòm)
      const P = W.__PL;
      if (!P || !safe(() => P.UI.isOpen('scr-item'), false)) { itemSeenAt = 0; return; }
      const cards = [...document.querySelectorAll('#item-cards .card')];
      if (cards.length < 2) return;
      const now = Date.now();
      if (!itemSeenAt) { itemSeenAt = now; return; }
      if (now - itemSeenAt < 700 || now - itemActAt < 700) return;
      const cur = safe(() => P.Game.player.item, null) || itemIdFromCard(P, cards[0]);
      const nxt = itemIdFromCard(P, cards[1]);
      const rn = itemRank(nxt), rc = itemRank(cur);
      let idx = 0, why = 'giữ nguyên / bỏ qua';
      if (nxt && rn < rc) { idx = 1; why = cur ? 'đổi sang món ưu tiên cao hơn' : 'nhận món đã chọn'; }
      else if (cur && cards[2] && state.itemLock && rc !== Infinity && SHOP_ORDER.every(id => itemRank(id) >= rc)) { idx = 2; why = 'khóa món ưu tiên cao nhất'; }
      itemActAt = now;
      console.info(`${TAG} Item: đang cầm ${cur || '—'}, món mới ${nxt || '?'} → ${why}`);
      cards[idx].click();
    } catch (e) { console.warn(`${TAG} item:`, e); }
  }, 150);

  // v0.9.14: CHẠY NỀN THẬT. Game chỉ tự chạy khi ẩn tab nếu bật tùy chọn bgPlay của chính nó, và bộ hẹn giờ nền của game
  // tự hủy sau mỗi màn thẻ/item/rift (không tự bật lại) => bật bgPlay + kích lại bộ hẹn giờ + âm thanh im lặng chống giảm tốc.
  let bgOrig = null, bgKickAt = 0, bgLastT = null, bgLastTAt = 0, bgAudio = null;
  function startKeepAudio() {
    if (!state.bgAudio) { stopKeepAudio(); return; }
    if (bgAudio) { if (bgAudio.ctx.state === 'suspended') safe(() => bgAudio.ctx.resume(), null); return; }
    try {
      const AC = W.AudioContext || W.webkitAudioContext; if (!AC) return;
      const ctx = new AC(), osc = ctx.createOscillator(), gain = ctx.createGain();
      osc.frequency.value = 20; gain.gain.value = 0.002; osc.connect(gain); gain.connect(ctx.destination); osc.start();
      bgAudio = { ctx };
    } catch (_) { bgAudio = { ctx: { state: 'closed', resume() {}, suspend() {} } }; }
  }
  function stopKeepAudio() { if (bgAudio && bgAudio.ctx.state === 'running') safe(() => bgAudio.ctx.suspend(), null); }
  function backgroundKeep(P) {
    const want = !!(state.background && state.enabled && !isIOS);
    const S = P.Settings;
    if (S && typeof S.get === 'function' && typeof S.set === 'function') {
      const cur = safe(() => S.get('bgPlay'), null);
      if (want && cur === false) { bgOrig = false; safe(() => S.set('bgPlay', true), null); }
      else if (!want && bgOrig !== null && cur === true) { safe(() => S.set('bgPlay', bgOrig), null); bgOrig = null; }
    }
    if (want && document.hidden) {
      startKeepAudio();
      const now = Date.now(), t = safe(() => P.Game.st.time, null);
      if (t !== bgLastT) { bgLastT = t; bgLastTAt = now; }
      else if (P.Game.state === 'playing' && !safe(() => P.Coop.active, false) && now - bgLastTAt > 1500 && now - bgKickAt > 1500) {
        bgKickAt = now; safe(() => document.dispatchEvent(new Event('visibilitychange')), null);   // game: ẩn + bgPlay + playing => tạo lại bộ hẹn giờ nền (đã có thì bỏ qua)
      }
    } else { stopKeepAudio(); bgLastT = null; }
  }

  let uiTick = 0;
  setInterval(() => {
    const P = W.__PL;
    if (!P) return;
    install(P);
    shopTick(P);
    try {
      const o = pendingCardOffer, nowT = Date.now();
      if (state.autoPick && state.enabled && o && !o.done && o.options.length && nowT - o.at >= 700 && nowT - o.lastTry >= 400) {
        o.lastTry = nowT; o.tries++;
        const scores = o.options.map((x, i) => scoreCard(x, i));
        const best = scores.reduce((b, sc, i) => sc > scores[b] ? i : b, 0);
        if (!o.rerolled && ((state.reroll && scores[best] < 150) || (state.cardPick && state.cardReroll && cardHasPrefs() && scores[best] < 3000)) && safe(() => P.RunUI.rerollsLeft(), 0) > 0 && typeof P.RunUI.reroll === 'function') {
          o.rerolled = true; o.at = nowT; safe(() => P.RunUI.reroll(), null);
        } else safe(() => P.RunUI.pick(best), null);
        if (o.tries > 8) o.done = true;
      }
    } catch (_) {}
    runLog.sample();
    panel();

    syncEnabledUI();
    {
      const pl = P.Game.player, hpf = document.getElementById('plh-hpfill'), hpt = document.getElementById('plh-hptxt'), pill = document.getElementById('plh-pill');
      if (hpf && pl) { const r = Math.max(0, Math.min(1, (pl.hp || 0) / Math.max(1, pl.maxHp || 1))); hpf.style.width = (r * 100).toFixed(0) + '%'; hpf.style.background = r > 0.6 ? 'var(--ok)' : r > 0.3 ? 'var(--warn)' : 'var(--bad)'; if (hpt) hpt.textContent = `${Math.round(pl.hp || 0)} / ${Math.round(pl.maxHp || 0)}`; }
      if (pill) pill.textContent = `v${VERSION} · ${state.enabled ? botMode : 'bạn tự chơi'}` + (state.enabled && Date.now() < us.warnUntil ? ' ⚠ ' + us.warn : '') + (safe(() => P.Coop.active, false) ? ' · co-op' : '');
    }

    const status = document.getElementById('plh-status');
    if (status && !panelPrefs.hidden) {
      const p = P.Game.player, ctx = makeStatusCounts(P);
      const goalPosStr = goalState.goal ? ` (${goalState.goal.x.toFixed(0)},${goalState.goal.y.toFixed(0)})` : '';
      uiTick = (uiTick + 1) % 2; if (!uiTick) drawMinimap(P);
      const pf = document.getElementById('plh-perf');
      if (pf) pf.textContent = `⚡ AI ${perf.avg.toFixed(1)}ms (đỉnh ${perf.max.toFixed(0)}) · ${perf.fps} FPS · nhịp ${perf.interval}ms · bỏ qua ${perf.calls + perf.skipped ? Math.round(100 * perf.skipped / (perf.calls + perf.skipped)) : 0}%`;
      status.textContent = `${eventInfo.name ? '[' + eventInfo.name + '] ' : ''}${state.enabled ? 'BOT ON' : 'BOT OFF'} | ${botMode} | HP ${p?.hp ?? '?'} / ${p?.maxHp ?? '?'} | ${currentTarget || 'không mục tiêu'}${goalPosStr} — ${targetReason || ''} | quái ${ctx.enemies} · đạn ${ctx.shots}`;
    }

    backgroundKeep(P);
    if (state.background && state.enabled && P.Game.state === 'paused') safe(() => P.Game.togglePause(), null);

    if (state.autoRestart && P.Game.state === 'over' && !restartRequested) {
      restartRequested = true;
      // v0.9.6: chờ cố định (mặc định 10s) ở màn tổng kết rồi mới chơi ván mới
      const waitMs = clamp(Number(state.restartDelay) || 10, 3, 60) * 1000;
      setTimeout(() => { if (state.autoRestart && W.__PL?.Game?.state === 'over') safe(() => W.__PL.Game.startRun(), null); }, waitMs);
    } else if (P.Game.state !== 'over') restartRequested = false;
  }, 250);

  // PokéLoop: game tự mở sẵn window.__offlineGame (cùng bộ module với PokéLit) => không cần viết lại trang.
  // KHAI ĐÚNG: khi bot đang chạy ván, PokeLoopAutoRun() trả về true để báo cáo ván của game ghi cờ auto=true.
  function installAutoFlag() {
    const mark = () => {
      const cur = W.PokeLoopAutoRun;
      if (typeof cur !== 'function' || cur.__plbWrapped) return;
      const wrapped = () => { try { if (state.enabled && W.__PL?.Game?.state === 'playing') return true; } catch (_) {} return !!cur(); };
      wrapped.__plbWrapped = true; try { W.PokeLoopAutoRun = wrapped; } catch (_) {}
    };
    mark(); setInterval(mark, 1000);
  }
  (function attachToGame() {
    const started = Date.now();
    const wait = setInterval(() => {
      try {
        const G = W.__offlineGame;
        if (G && G.Game && G.Input && G.World && G.EnemyMgr && document.body) {
          clearInterval(wait);
          W.__PL = G;
          setBootStatus('Có __offlineGame; đang khởi tạo Bot…');
          install(G);
          panel();
          installAutoFlag();
          setTimeout(() => { try { document.getElementById('plh-boot-status')?.remove(); } catch (_) {} }, 3000);
        } else if (Date.now() - started > 60000) {
          clearInterval(wait);
          setBootStatus('Không thấy window.__offlineGame sau 60 giây (game đổi cấu trúc?)', true);
          console.error(`${TAG} Không thấy window.__offlineGame`);
        }
      } catch (e) { clearInterval(wait); setBootStatus('Lỗi khởi tạo: ' + (e.message || e), true); console.error(TAG, e); }
    }, 100);
  })();
})();