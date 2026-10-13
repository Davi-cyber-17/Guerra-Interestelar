'use strict';
/* =====================================================================
   Guerra Interestelar
   - Modo Local: 1 jogador
   - Modo Online: sala com até 2 jogadores (cooperativo) via WebRTC (PeerJS).
     Funciona entre dispositivos diferentes (PC, celular, tablet).
     O anfitrião roda o jogo; o convidado envia a posição da nave e
     recebe o estado do jogo (com suavização/extrapolação).
   ===================================================================== */

const W = 360, H = 640;
const $ = id => document.getElementById(id);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const rnd = (a, b) => a + Math.random() * (b - a);
const MAXP = 12;
const FH = '700 12px Orbitron, "Trebuchet MS", sans-serif';

const cv = $('game'), ctx = cv.getContext('2d');
let K = 2;                       // escala interna do canvas (nítido em qualquer tela)
cv.width = W * K; cv.height = H * K;

/* ---------------------------- estado global --------------------------- */
let mode = 'local';              // 'local' | 'host' | 'guest'
let G = null, V = null;
let myIdx = 0, inGame = false, running = false;
let T = 0, last = 0;
let me = { x: W / 2, y: H - 110, tx: W / 2, ty: H - 110 };
const keys = {};
let parts = [], rp = [];
let evLocal = [], evNet = [];
let snapAcc = 0, inAcc = 0, shootAcc = 0, pingAcc = 0, snapT = 0;
let lastLevel = 0, bannerT = 0, bannerTxt = '', overShown = false;
let netPing = 0;
let net = { peer: null, conn: null, role: null, code: '' };
const isTouch = matchMedia('(pointer:coarse)').matches;

let best = 0;
try { best = +localStorage.getItem('gxs_best') || 0; } catch (e) {}
$('bestScore').textContent = best;
$('helpText').innerHTML = isTouch
  ? 'Arraste o dedo na tela para mover a nave.<br>Ela atira sozinha. Pegue ⚡ para mais poder.'
  : 'Mova a nave com o <b>mouse</b> ou <b>WASD/setas</b>.<br>Ela atira sozinha. Pegue ⚡ para mais poder.';

/* ------------------------------- áudio -------------------------------- */
let AC = null, muted = false;
function tone(type, f1, f2, dur, vol) {
  if (muted) return;
  try {
    AC = AC || new (window.AudioContext || window.webkitAudioContext)();
    if (AC.state === 'suspended') AC.resume();
    const o = AC.createOscillator(), g = AC.createGain(), t = AC.currentTime;
    o.type = type;
    o.frequency.setValueAtTime(f1, t);
    o.frequency.exponentialRampToValueAtTime(Math.max(1, f2), t + dur);
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g); g.connect(AC.destination);
    o.start(t); o.stop(t + dur);
  } catch (e) {}
}
const SFX = {
  shoot: () => tone('square', 900, 500, 0.05, 0.012),
  hit:   () => tone('triangle', 300, 200, 0.05, 0.04),
  boom:  () => tone('sawtooth', 200, 40, 0.28, 0.06),
  coin:  () => { tone('sine', 988, 988, 0.07, 0.05); setTimeout(() => tone('sine', 1319, 1319, 0.12, 0.05), 70); },
  pow:   () => tone('triangle', 400, 1400, 0.25, 0.06),
  hurt:  () => tone('sawtooth', 320, 50, 0.5, 0.08)
};

/* ------------------------------- telas -------------------------------- */
function show(id) {
  document.querySelectorAll('.screen').forEach(s => s.classList.toggle('active', s.id === id));
  fit();
}
let toastTimer = null;
function toast(msg) {
  const t = $('toast');
  t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), 2800);
}

/* Responsivo: calcula o maior tamanho 9:16 que cabe, com nitidez por DPR */
function fit() {
  document.documentElement.style.setProperty('--vh', innerHeight + 'px');
  const st = $('stage');
  if (!st.classList.contains('active')) return;
  const cs = getComputedStyle(st);
  const sL = $('sideL'), sR = $('sideR');
  const sides = sL.offsetWidth + sR.offsetWidth + (sL.offsetWidth ? 80 : 0);
  const availW = st.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight) - sides - (sides ? 0 : 0);
  const availH = st.clientHeight - parseFloat(cs.paddingTop) - parseFloat(cs.paddingBottom) - (sides ? 24 : 0);
  const s = Math.max(0.25, Math.min(availW / W, availH / H));
  const w = Math.floor(W * s), h = Math.floor(H * s);
  $('wrap').style.width = w + 'px';
  $('wrap').style.height = h + 'px';
  const dpr = Math.min(window.devicePixelRatio || 1, 2.5);
  const nw = Math.round(clamp(w * dpr, 360, 1100));
  if (cv.width !== nw) { cv.width = nw; cv.height = Math.round(H * nw / W); }
  K = cv.width / W;
}
addEventListener('resize', fit);
addEventListener('orientationchange', () => setTimeout(fit, 200));
if (window.visualViewport) visualViewport.addEventListener('resize', fit);
document.addEventListener('fullscreenchange', () => setTimeout(fit, 100));
document.addEventListener('webkitfullscreenchange', () => setTimeout(fit, 100));
['gesturestart', 'gesturechange'].forEach(ev => document.addEventListener(ev, e => e.preventDefault()));

/* manter a tela ligada durante o jogo (celular) */
let wl = null;
async function lockScreen() {
  try { if ('wakeLock' in navigator && !wl) { wl = await navigator.wakeLock.request('screen'); wl.addEventListener('release', () => { wl = null; }); } } catch (e) {}
}
function unlockScreen() { try { wl && wl.release(); } catch (e) {} wl = null; }
document.addEventListener('visibilitychange', () => { if (!document.hidden && inGame) lockScreen(); });

/* ============================== SIMULAÇÃO ============================== */
function mkPlayer(i, n) {
  const x = n === 2 ? (i ? W / 2 + 50 : W / 2 - 50) : W / 2;
  return { i, x, y: H - 110, tx: undefined, ty: undefined, lives: 3, shield: 3, power: 1, coins: 0, score: 0, alive: true, resp: 0, fire: 0 };
}

function newGame(n) {
  G = { t: 0, level: 1, state: 'play', stateT: 0, eggT: 1.5, players: [], enemies: [], bullets: [], eggs: [], drops: [] };
  for (let i = 0; i < n; i++) G.players.push(mkPlayer(i, n));
  spawnWave();
}

function spawnWave() {
  const L = G.level, n = G.players.length;
  G.enemies = []; G.eggs = []; G.bullets = [];
  if (L % 5 === 0) {
    const hp = Math.round((40 + L * 6) * (n === 2 ? 1.7 : 1));
    G.enemies.push({ x: W / 2, y: -120, hx: W / 2, hy: 115, type: 3, boss: true, hp, maxhp: hp, ph: 0 });
  } else {
    const rows = Math.min(3 + Math.floor(L / 4), 6);
    const cols = Math.min(5 + Math.floor(L / 3), 7);
    const hp = 1 + Math.floor(L / 3) + (n === 2 && L >= 3 ? 1 : 0);
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const hx = W / 2 + (c - (cols - 1) / 2) * 44;
        const hy = 80 + r * 44;
        G.enemies.push({ x: hx + rnd(-30, 30), y: -40 - r * 40 - c * 8, hx, hy, type: (r + c) % 3, boss: false, hp, maxhp: hp, ph: rnd(0, 6) });
      }
    }
  }
}

function addEv(a) { evLocal.push(a); if (mode === 'host') evNet.push(a); }
function checkOver() { if (G.players.every(p => p.lives <= 0)) G.state = 'over'; }

function hurt(p) {
  if (!p.alive || p.shield > 0) return;
  p.lives--; p.alive = false; p.resp = 1.4;
  p.power = Math.max(1, p.power - 2);
  addEv(['boom', p.x, p.y, 1]); addEv(['hurt']);
  checkOver();
}

function kill(e, owner) {
  const p = G.players[owner] || G.players[0];
  p.score += e.boss ? 500 + G.level * 20 : 10 + G.level * 2;
  addEv(['boom', e.x, e.y, e.boss ? 1 : 0]);
  if (e.boss) {
    for (let i = 0; i < 14; i++) G.drops.push({ x: e.x + rnd(-50, 50), y: e.y + rnd(-30, 30), k: 0, vy: rnd(60, 110) });
    G.drops.push({ x: e.x, y: e.y, k: 1, vy: 80 });
  } else {
    if (Math.random() < 0.38) G.drops.push({ x: e.x, y: e.y, k: 0, vy: 90 });
    if (Math.random() < 0.09) G.drops.push({ x: e.x, y: e.y, k: 1, vy: 80 });
  }
}

function step(dt) {
  G.t += dt;
  if (G.state === 'over') return;

  for (const p of G.players) {
    if (!p.alive) {
      if (p.lives > 0) {
        p.resp -= dt;
        if (p.resp <= 0) { p.alive = true; p.shield = 3; p.y = H - 110; if (p.i === myIdx) me.ty = H - 110; }
      }
      continue;
    }
    p.shield = Math.max(0, p.shield - dt);
    p.fire -= dt;
    if (p.fire <= 0) {
      p.fire = Math.max(0.12, 0.24 - p.power * 0.008);
      const n = Math.min(7, 1 + Math.floor(p.power / 2));
      for (let k = 0; k < n; k++) {
        const o = k - (n - 1) / 2;
        G.bullets.push({ x: p.x + o * 9, y: p.y - 22, vx: o * 9, vy: 560, dmg: 1, o: p.i });
      }
    }
  }

  const L = G.level;
  for (const e of G.enemies) {
    const amp = e.boss ? 100 : 18;
    const tx = e.hx + Math.sin(G.t * (e.boss ? 0.8 : 0.9)) * amp;
    const ty = e.hy + (e.boss ? 0 : Math.sin(G.t * 1.3 + e.hx * 0.05) * 6);
    const k = Math.min(1, dt * 3);
    e.x += (tx - e.x) * k; e.y += (ty - e.y) * k;
  }

  G.eggT -= dt;
  const settled = G.enemies.filter(e => e.y > 20);
  if (G.eggT <= 0 && settled.length && G.state === 'play') {
    const boss = settled.find(e => e.boss);
    if (boss) {
      const n = 3 + Math.min(4, Math.floor(L / 5));
      for (let i = 0; i < n; i++) {
        const a = (i - (n - 1) / 2) * 0.28, sp = 170 + L * 3;
        G.eggs.push({ x: boss.x, y: boss.y + 40, vx: Math.sin(a) * sp, vy: Math.cos(a) * sp });
      }
      G.eggT = Math.max(0.9, 1.6 - L * 0.02);
    } else {
      const e = settled[Math.floor(Math.random() * settled.length)];
      G.eggs.push({ x: e.x, y: e.y + 12, vx: 0, vy: 150 + L * 5 });
      G.eggT = Math.max(0.28, 1.1 - L * 0.05);
    }
  }

  for (let i = G.eggs.length - 1; i >= 0; i--) {
    const g = G.eggs[i];
    g.x += g.vx * dt; g.y += g.vy * dt;
    if (g.y > H + 20 || g.x < -20 || g.x > W + 20) { G.eggs.splice(i, 1); continue; }
    for (const p of G.players) {
      if (p.alive && p.shield <= 0 && Math.hypot(p.x - g.x, p.y - g.y) < 17) { G.eggs.splice(i, 1); hurt(p); break; }
    }
  }

  for (let bi = G.bullets.length - 1; bi >= 0; bi--) {
    const b = G.bullets[bi];
    b.x += b.vx * dt; b.y -= b.vy * dt;
    if (b.y < -20 || b.x < -10 || b.x > W + 10) { G.bullets.splice(bi, 1); continue; }
    for (const e of G.enemies) {
      if (e.dead) continue;
      const r = e.boss ? 46 : 17;
      if (Math.abs(b.x - e.x) < r && Math.abs(b.y - e.y) < r) {
        e.hp -= b.dmg; G.bullets.splice(bi, 1);
        addEv(['hit', b.x, b.y]);
        if (e.hp <= 0) { e.dead = true; kill(e, b.o); }
        break;
      }
    }
  }
  G.enemies = G.enemies.filter(e => !e.dead);

  for (const p of G.players) {
    if (!p.alive || p.shield > 0) continue;
    for (const e of G.enemies) {
      const r = (e.boss ? 46 : 18) + 8;
      if (Math.abs(p.x - e.x) < r && Math.abs(p.y - e.y) < r) { hurt(p); break; }
    }
  }

  for (let i = G.drops.length - 1; i >= 0; i--) {
    const d = G.drops[i];
    d.y += d.vy * dt;
    if (d.y > H + 20) { G.drops.splice(i, 1); continue; }
    for (const p of G.players) {
      if (p.alive && Math.hypot(p.x - d.x, p.y - d.y) < 28) {
        if (d.k === 0) { p.coins++; p.score += 5; addEv(['coin', d.x, d.y]); }
        else { p.power = Math.min(MAXP, p.power + 1); p.score += 20; addEv(['pow', d.x, d.y]); }
        G.drops.splice(i, 1); break;
      }
    }
  }

  if (G.state === 'play' && G.enemies.length === 0) {
    G.state = 'clear'; G.stateT = 2.4;
    for (const p of G.players) if (p.alive) p.score += 100 * G.level;
  } else if (G.state === 'clear') {
    G.stateT -= dt;
    if (G.stateT <= 0) { G.level++; spawnWave(); G.state = 'play'; G.eggT = 1.5; }
  }
}

/* =============================== REDE ================================== */
/* STUN + TURN (relay) ajudam a conectar PC <-> celular em redes diferentes */
const PEER_OPTS = {
  config: {
    iceServers: [
      { urls: 'stun:stun.l.google.com:19302' },
      { urls: 'stun:stun1.l.google.com:19302' },
      { urls: 'stun:global.stun.twilio.com:3478' },
      { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turn:openrelay.metered.ca:443?transport=tcp'],
        username: 'openrelayproject', credential: 'openrelayproject' }
    ]
  }
};

function genCode() {
  const c = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let s = '';
  for (let i = 0; i < 5; i++) s += c[Math.floor(Math.random() * c.length)];
  return s;
}
function send(obj) { try { if (net.conn && net.conn.open) net.conn.send(obj); } catch (e) {} }
function cleanupNet() {
  const { peer, conn } = net;
  net = { peer: null, conn: null, role: null, code: '' };
  netPing = 0;
  try { conn && conn.close(); } catch (e) {}
  try { peer && peer.destroy(); } catch (e) {}
}
addEventListener('pagehide', cleanupNet);
function netMsg(id, text, ok) { const el = $(id); el.textContent = text || ''; el.classList.toggle('ok', !!ok); }
function libOk() {
  if (typeof Peer === 'undefined') { netMsg('onlineMsg', 'Não foi possível carregar a biblioteca de rede. Verifique sua internet.'); return false; }
  return true;
}

function createRoom(tries = 0) {
  if (!libOk()) return;
  cleanupNet();
  netMsg('onlineMsg', 'Criando sala…', true);
  const code = genCode();
  const peer = new Peer('gxs-' + code, PEER_OPTS);
  net.peer = peer; net.code = code; net.role = 'host';
  peer.on('open', () => { if (net.peer !== peer) return; netMsg('onlineMsg', ''); showLobby(); });
  peer.on('error', err => {
    if (net.peer !== peer) return;
    if (err.type === 'unavailable-id' && tries < 5) return createRoom(tries + 1);
    cleanupNet(); netMsg('onlineMsg', 'Erro ao criar a sala (' + err.type + '). Tente de novo.'); show('online');
  });
  peer.on('connection', conn => {
    if (net.peer !== peer) return;
    if (net.conn && net.conn.open) {
      conn.on('open', () => { conn.send({ t: 'full' }); setTimeout(() => conn.close(), 300); });
      return;
    }
    net.conn = conn; setupConn(conn);
  });
  peer.on('disconnected', () => { try { peer.reconnect(); } catch (e) {} });
}

function joinRoom(raw) {
  const code = (raw || '').trim().toUpperCase();
  if (code.length < 5) return netMsg('onlineMsg', 'Digite o código de 5 letras/números da sala.');
  if (!libOk()) return;
  cleanupNet();
  netMsg('onlineMsg', 'Conectando à sala…', true);
  const peer = new Peer(PEER_OPTS);
  net.peer = peer; net.code = code; net.role = 'guest';
  const fail = msg => { if (net.peer !== peer) return; cleanupNet(); netMsg('onlineMsg', msg); show('online'); };
  peer.on('open', () => {
    if (net.peer !== peer) return;
    const conn = peer.connect('gxs-' + code, { serialization: 'json' });
    net.conn = conn; setupConn(conn);
    setTimeout(() => { if (net.peer === peer && !conn.open) fail('Não foi possível entrar na sala. Confira o código e tente de novo.'); }, 15000);
  });
  peer.on('error', err => fail(err.type === 'peer-unavailable' ? 'Sala não encontrada. Confira o código.' : 'Erro de conexão (' + err.type + ').'));
}

function setupConn(conn) {
  conn.on('open', () => {
    if (net.conn !== conn) return;
    if (net.role === 'guest') { send({ t: 'hello' }); showLobby(); }
    else { updateLobby(); toast('Jogador 2 entrou na sala!'); }
  });
  conn.on('data', onData);
  conn.on('close', () => { if (net.conn === conn) onClose(); });
  conn.on('error', () => { if (net.conn === conn) onClose(); });
}

function onData(d) {
  if (!d || !d.t) return;
  if (net.role === 'host') {
    if (d.t === 'in' && G && G.players[1]) {
      const p = G.players[1];
      p.tx = clamp(+d.x || 0, 16, W - 16); p.ty = clamp(+d.y || 0, 40, H - 30);
      if (!p.alive) { p.x = p.tx; p.y = p.ty; }
    } else if (d.t === 'ping') send({ t: 'pong', ts: d.ts });
  } else if (net.role === 'guest') {
    if (d.t === 'full') { cleanupNet(); netMsg('onlineMsg', 'A sala está cheia.'); show('online'); }
    else if (d.t === 'start') startGuest();
    else if (d.t === 's') onSnap(d);
    else if (d.t === 'pong') { const r = performance.now() - d.ts; netPing = netPing ? netPing * 0.6 + r * 0.4 : r; updateSide(); }
  }
}

function onClose() {
  if (net.role === 'host') {
    net.conn = null;
    if (inGame && G) { const p = G.players[1]; if (p) { p.lives = 0; p.alive = false; } checkOver(); }
    else updateLobby();
    toast('O jogador 2 saiu da sala.');
  } else {
    toast('O anfitrião saiu da sala.');
    leaveToMenu();
  }
}

/* ------------------------------- lobby -------------------------------- */
function showLobby() { $('lobbyCode').textContent = net.code; show('lobby'); updateLobby(); }
function updateLobby() {
  const ul = $('lobbyPlayers');
  const host = net.role === 'host';
  const connected = net.conn && net.conn.open;
  if (host) {
    ul.innerHTML = '<li>👑 Você (anfitrião) ✔</li>' + (connected ? '<li>🚀 Jogador 2 ✔</li>' : '<li class="wait">Aguardando jogador 2…</li>');
    $('btnStartOnline').style.display = '';
    $('btnStartOnline').disabled = !connected;
    netMsg('lobbyMsg', connected ? 'Tudo pronto! Inicie o jogo.' : 'Envie o código ou o link para seu amigo.', connected);
  } else {
    ul.innerHTML = '<li>👑 Anfitrião ✔</li><li>🚀 Você ✔</li>';
    $('btnStartOnline').style.display = 'none';
    netMsg('lobbyMsg', 'Aguardando o anfitrião iniciar o jogo…', true);
  }
}
function updateSide() {
  $('sideMode').textContent = mode === 'local' ? 'LOCAL' : mode === 'host' ? 'ANFITRIÃO' : 'CONVIDADO';
  $('sideRoom').textContent = net.code || '—';
  $('sidePing').textContent = mode === 'guest' ? (netPing ? Math.round(netPing) + ' ms' : '…') : mode === 'host' ? 'ONLINE' : '—';
}

/* ============================ INÍCIO DE JOGO =========================== */
function enterGame() {
  show('stage');
  $('over').classList.remove('show');
  overShown = false; lastLevel = 0; bannerT = 0;
  parts = []; rings = []; rp = []; evLocal = []; evNet = [];
  me = { x: W / 2, y: H - 110, tx: W / 2, ty: H - 110 };
  inGame = true;
  try { document.fonts && document.fonts.load('700 12px Orbitron'); } catch (e) {}
  updateSide(); lockScreen(); fit();
  if (!running) { running = true; last = performance.now(); requestAnimationFrame(loop); }
}
function startLocal() { mode = 'local'; myIdx = 0; newGame(1); V = G; enterGame(); }
function startHost() {
  if (!(net.conn && net.conn.open)) return;
  mode = 'host'; myIdx = 0; newGame(2); V = G;
  send({ t: 'start' });
  enterGame();
}
function startGuest() {
  mode = 'guest'; myIdx = 1; G = null; V = null;
  enterGame();
  me.x = me.tx = W / 2 + 50;
}
function leaveToMenu() {
  inGame = false; unlockScreen();
  cleanupNet();
  $('over').classList.remove('show');
  $('bestScore').textContent = best;
  show('menu');
}

/* =============================== ENTRADA =============================== */
function setPtr(e) {
  const r = cv.getBoundingClientRect();
  me.tx = clamp((e.clientX - r.left) / r.width * W, 16, W - 16);
  const off = e.pointerType === 'mouse' ? 0 : 55;       // dedo não cobre a nave
  me.ty = clamp((e.clientY - r.top) / r.height * H - off, 50, H - 40);
}
cv.addEventListener('pointerdown', e => { try { cv.setPointerCapture(e.pointerId); } catch (_) {} setPtr(e); });
cv.addEventListener('pointermove', e => { if (e.pointerType === 'mouse' || e.buttons || e.pressure > 0) setPtr(e); });
cv.addEventListener('contextmenu', e => e.preventDefault());
addEventListener('keydown', e => {
  const k = e.key.toLowerCase();
  if (inGame && ['arrowup', 'arrowdown', 'arrowleft', 'arrowright', ' '].includes(k)) e.preventDefault();
  keys[k] = true;
});
addEventListener('keyup', e => { keys[e.key.toLowerCase()] = false; });
addEventListener('blur', () => { for (const k in keys) keys[k] = false; });
function readKeys(dt) {
  const sp = 380 * dt;
  if (keys['arrowleft'] || keys['a']) me.tx -= sp;
  if (keys['arrowright'] || keys['d']) me.tx += sp;
  if (keys['arrowup'] || keys['w']) me.ty -= sp;
  if (keys['arrowdown'] || keys['s']) me.ty += sp;
  me.tx = clamp(me.tx, 16, W - 16);
  me.ty = clamp(me.ty, 50, H - 40);
}

/* ============================ SNAPSHOT (rede) ========================== */
function snapshot() {
  const r = Math.round;
  const s = {
    t: 's', l: G.level, st: G.state,
    p: G.players.map(p => [r(p.x), r(p.y), p.lives, +p.shield.toFixed(1), p.power, p.coins, p.score, p.alive ? 1 : 0]),
    e: G.enemies.map(e => [r(e.x), r(e.y), e.type, Math.max(0, r(e.hp / e.maxhp * 100)), e.boss ? 1 : 0]),
    b: G.bullets.map(b => [r(b.x), r(b.y), r(b.vx)]),
    x: G.eggs.map(g => [r(g.x), r(g.y), r(g.vx), r(g.vy)]),
    g: G.drops.map(d => [r(d.x), r(d.y), d.k, r(d.vy)]),
    ev: evNet
  };
  evNet = [];
  return s;
}
function onSnap(d) {
  V = {
    level: d.l, state: d.st,
    players: d.p.map(a => ({ x: a[0], y: a[1], lives: a[2], shield: a[3], power: a[4], coins: a[5], score: a[6], alive: !!a[7] })),
    enemies: d.e.map(a => ({ x: a[0], y: a[1], type: a[2], hp: a[3], maxhp: 100, boss: !!a[4] })),
    bullets: d.b.map(a => ({ x: a[0], y: a[1], vx: a[2], vy: 560 })),
    eggs: d.x.map(a => ({ x: a[0], y: a[1], vx: a[2], vy: a[3] })),
    drops: d.g.map(a => ({ x: a[0], y: a[1], k: a[2], vy: a[3] }))
  };
  snapT = performance.now();
  processEvents(d.ev);
}

/* ================================ LOOP ================================= */
function loop(now) {
  if (!inGame) { running = false; return; }
  const dt = Math.min(0.05, (now - last) / 1000);
  last = now; T += dt;
  readKeys(dt);

  if (mode === 'guest') {
    const k = Math.min(1, dt * 14);
    me.x += (me.tx - me.x) * k; me.y += (me.ty - me.y) * k;
    inAcc += dt;
    if (inAcc >= 0.033) { inAcc = 0; send({ t: 'in', x: me.x, y: me.y }); }
    pingAcc += dt;
    if (pingAcc >= 2) { pingAcc = 0; send({ t: 'ping', ts: performance.now() }); }
  } else {
    const mp = G.players[myIdx];
    if (mp.alive) {
      const k = Math.min(1, dt * 14);
      mp.x += (me.tx - mp.x) * k; mp.y += (me.ty - mp.y) * k;
    }
    const rpl = mode === 'host' ? G.players[1] : null;       // jogador remoto: suaviza
    if (rpl && rpl.alive && rpl.tx !== undefined) {
      const k = Math.min(1, dt * 20);
      rpl.x += (rpl.tx - rpl.x) * k; rpl.y += (rpl.ty - rpl.y) * k;
    }
    step(dt);
    if (mode === 'host') {
      snapAcc += dt;
      if (snapAcc >= 0.033) { snapAcc = 0; send(snapshot()); }
    }
    processEvents(evLocal); evLocal = [];
  }

  shootAcc += dt;
  if (shootAcc > 0.24) {
    shootAcc = 0;
    const p = V && V.players[myIdx];
    if (p && p.alive && V.state === 'play') SFX.shoot();
  }

  render(dt, now);
  requestAnimationFrame(loop);
}

/* ============================== PARTÍCULAS ============================= */
function burst(x, y, n, cols, sp) {
  for (let i = 0; i < n; i++) {
    const a = Math.random() * 6.283, s = rnd(sp * 0.2, sp);
    parts.push({ x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, life: rnd(0.3, 0.7), max: 0.7, c: cols[i % cols.length], r: rnd(1.5, 3.5) });
  }
  if (parts.length > 350) parts.splice(0, parts.length - 350);
}
function processEvents(list) {
  if (!list) return;
  for (const e of list) {
    const k = e[0], x = e[1], y = e[2], big = e[3];
    if (k === 'boom') {
      burst(x, y, big ? 54 : 18, ['#ffffff', '#ffe08a', '#ffb300', '#ff6a1f', '#ff3b1f'], big ? 260 : 160);
      rings.push({ x, y, r: big ? 130 : 50, life: big ? 0.7 : 0.4, max: big ? 0.7 : 0.4, c: big ? '#ffb347' : '#ff8a3a' });
      if (big) rings.push({ x, y, r: 80, life: 0.5, max: 0.5, c: '#fff' });
      if (rings.length > 30) rings.splice(0, rings.length - 30);
      SFX.boom();
    }
    else if (k === 'hit') { burst(x, y, 3, ['#7fe9ff', '#ffffff', '#ffd54a'], 90); if (Math.random() < 0.4) SFX.hit(); }
    else if (k === 'coin') { burst(x, y, 6, ['#ffd54a', '#fff2a0'], 90); SFX.coin(); }
    else if (k === 'pow') { burst(x, y, 12, ['#00e5ff', '#ffffff'], 140); SFX.pow(); }
    else if (k === 'hurt') SFX.hurt();
  }
}

/* ============================== DESENHO ================================ */
function mkGlow(rgb) {
  const c = document.createElement('canvas'); c.width = c.height = 64;
  const g = c.getContext('2d'), gr = g.createRadialGradient(32, 32, 0, 32, 32, 32);
  gr.addColorStop(0, 'rgba(' + rgb + ',1)'); gr.addColorStop(0.35, 'rgba(' + rgb + ',.35)'); gr.addColorStop(1, 'rgba(' + rgb + ',0)');
  g.fillStyle = gr; g.fillRect(0, 0, 64, 64);
  return c;
}
const GL_C = mkGlow('0,229,255'), GL_O = mkGlow('255,170,40'), GL_M = mkGlow('255,43,214'),
      GL_R = mkGlow('255,60,40'), GL_P = mkGlow('168,85,247'), GL_G = mkGlow('132,204,22'), GL_B = mkGlow('40,120,255');

let rings = [];   // ondas de choque das explosões

/* ---- fundos: nebulosas coloridas com planetas (um por "mundo") ---- */
function planet(c, x, y, r, c1, c2, c3, ring) {
  if (ring) {   // metade de trás do anel
    c.save(); c.translate(x, y); c.rotate(-0.35); c.scale(1, 0.28);
    c.strokeStyle = ring; c.globalAlpha = 0.55; c.lineWidth = r * 0.22;
    c.beginPath(); c.arc(0, 0, r * 1.55, Math.PI, 0); c.stroke(); c.restore();
  }
  const g = c.createRadialGradient(x - r * 0.4, y - r * 0.4, r * 0.1, x, y, r);
  g.addColorStop(0, c1); g.addColorStop(0.55, c2); g.addColorStop(1, c3);
  c.fillStyle = g; c.beginPath(); c.arc(x, y, r, 0, 7); c.fill();
  c.save(); c.beginPath(); c.arc(x, y, r, 0, 7); c.clip();
  c.globalAlpha = 0.16; c.fillStyle = '#000';                 // faixas / crateras
  for (let i = 0; i < 5; i++) { c.beginPath(); c.ellipse(x + rnd(-r, r) * 0.3, y + (i - 2) * r * 0.32, r * 1.2, r * 0.07, 0, 0, 7); c.fill(); }
  c.globalAlpha = 1;
  const sh = c.createRadialGradient(x - r * 0.5, y - r * 0.5, r * 0.4, x + r * 0.2, y + r * 0.2, r * 1.25);
  sh.addColorStop(0, 'rgba(0,0,0,0)'); sh.addColorStop(1, 'rgba(0,0,10,.82)');
  c.fillStyle = sh; c.fillRect(x - r, y - r, r * 2, r * 2);
  c.restore();
  c.strokeStyle = c2; c.globalAlpha = 0.5; c.lineWidth = 2; c.shadowColor = c1; c.shadowBlur = 14;
  c.beginPath(); c.arc(x, y, r, 0, 7); c.stroke(); c.globalAlpha = 1; c.shadowBlur = 0;
  if (ring) {   // metade da frente do anel
    c.save(); c.translate(x, y); c.rotate(-0.35); c.scale(1, 0.28);
    c.strokeStyle = ring; c.globalAlpha = 0.8; c.lineWidth = r * 0.22;
    c.beginPath(); c.arc(0, 0, r * 1.55, 0, Math.PI); c.stroke(); c.restore(); c.globalAlpha = 1;
  }
}
const THEMES = [
  { base: '#02070c', blobs: [[70, 240, 250, '25,170,80'], [310, 560, 220, '20,130,140'], [180, 940, 260, '90,50,200'], [40, 1180, 210, '30,170,90'], [320, 1250, 200, '120,60,220'], [250, 60, 170, '20,150,110']],
    planets: [[270, 760, 52, '#7be0ff', '#2a74c9', '#0a1d4a', null]] },
  { base: '#06021a', blobs: [[90, 200, 240, '130,50,210'], [310, 600, 230, '210,40,170'], [150, 980, 260, '70,60,230'], [60, 1200, 210, '200,50,160'], [330, 1260, 190, '110,40,200'], [250, 80, 160, '160,60,230']],
    planets: [[95, 520, 70, '#ffb48a', '#d0476a', '#3a0f3c', '#ffcf9a'], [290, 1150, 30, '#c9b6ff', '#6a4bd0', '#1a0d4a', null]] },
  { base: '#020820', blobs: [[80, 220, 240, '35,100,255'], [300, 540, 220, '0,170,255'], [170, 930, 270, '110,70,235'], [50, 1160, 210, '0,140,255'], [320, 1240, 190, '60,90,240'], [250, 70, 160, '0,190,255']],
    planets: [[250, 330, 44, '#ffd38a', '#e07a2a', '#40160a', null], [70, 1050, 80, '#9ae6ff', '#2f7fe0', '#07184a', '#8fd8ff']] },
  { base: '#0b0204', blobs: [[90, 230, 240, '210,40,40'], [310, 560, 220, '255,110,20'], [170, 940, 260, '150,30,120'], [50, 1170, 210, '230,60,30'], [320, 1250, 190, '170,40,140'], [250, 70, 160, '255,90,30']],
    planets: [[240, 700, 90, '#ffb36b', '#c9421f', '#2a0606', '#ff9a5a']] }
];
const nebulas = [];
function getNebula(i) {
  if (nebulas[i]) return nebulas[i];
  const T0 = THEMES[i], cv2 = document.createElement('canvas');
  cv2.width = W; cv2.height = H * 2;
  const c = cv2.getContext('2d');
  c.fillStyle = T0.base; c.fillRect(0, 0, W, H * 2);
  for (const [x, y, r, col] of T0.blobs) {
    for (const off of [-H * 2, 0, H * 2]) {
      const g = c.createRadialGradient(x, y + off, 0, x, y + off, r);
      g.addColorStop(0, 'rgba(' + col + ',0.55)'); g.addColorStop(0.5, 'rgba(' + col + ',0.2)'); g.addColorStop(1, 'rgba(' + col + ',0)');
      c.fillStyle = g; c.fillRect(0, 0, W, H * 2);
    }
  }
  c.fillStyle = '#fff';                                       // poeira de estrelas
  for (let k = 0; k < 160; k++) { c.globalAlpha = rnd(0.1, 0.5); c.fillRect(rnd(0, W), rnd(0, H * 2), 1, 1); }
  c.globalAlpha = 1;
  for (const p of T0.planets) planet(c, p[0], p[1], p[2], p[3], p[4], p[5], p[6]);
  return (nebulas[i] = cv2);
}
const stars = Array.from({ length: 90 }, () => ({ x: rnd(0, W), y: rnd(0, H), s: rnd(0.6, 2.4), v: rnd(20, 140), ph: rnd(0, 6) }));

/* ---- paletas ---- */
const PAL = [
  { hull: '#27c6dc', hullD: '#0b5a73', wing: '#ff8a1f', wingD: '#a8400a', glow: GL_C, flame: '#6cd8ff' },
  { hull: '#d03ae8', hullD: '#5e1470', wing: '#a6ef3a', wingD: '#4a7a10', glow: GL_M, flame: '#ff9cf0' }
];
const AL = [
  { w1: '#22d3ee', w2: '#0e6f8a', wv: '#c8f8ff', b1: '#ffb12a', b2: '#8a4a08', eye: '#fff7a8', gl: GL_C },
  { w1: '#b05cf5', w2: '#4d1a8a', wv: '#f0dcff', b1: '#ff7a2a', b2: '#7a2a08', eye: '#ffe45e', gl: GL_P },
  { w1: '#8fdc2a', w2: '#3c6a12', wv: '#ecffc4', b1: '#ff4a3a', b2: '#7a1410', eye: '#ffffff', gl: GL_G }
];

function drawBackground(dt) {
  const th = V ? (V.level % 5 === 0 ? 3 : (V.level - 1) % 3) : 2;
  const neb = getNebula(th);
  const sc = (T * 24) % (H * 2);
  ctx.drawImage(neb, 0, sc - H * 2);
  ctx.drawImage(neb, 0, sc);
  for (const s of stars) {
    s.y += s.v * dt; if (s.y > H) { s.y = -3; s.x = rnd(0, W); }
    const tw = 0.55 + 0.45 * Math.sin(T * 3 + s.ph);
    ctx.globalAlpha = (0.35 + s.s / 3.2) * tw;
    ctx.fillStyle = s.s > 1.9 ? '#bfe9ff' : '#fff';
    ctx.fillRect(s.x, s.y, s.s, s.s + (s.v > 100 ? 2 : 0));
  }
  ctx.globalAlpha = 1;
}

function glow(img, x, y, w, h, a) {
  ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = a == null ? 1 : a;
  ctx.drawImage(img, x - w / 2, y - h / 2, w, h);
  ctx.globalCompositeOperation = 'source-over'; ctx.globalAlpha = 1;
}

/* ---- nave do jogador ---- */
function drawShip(x, y, pi, shield, power) {
  const P = PAL[pi] || PAL[0], pw = power || 1;
  glow(P.glow, x, y + 24, 54, 70, 0.8);
  ctx.save(); ctx.translate(x, y);
  // chamas dos propulsores
  const fl = 14 + Math.sin(T * 45 + pi) * 4 + Math.random() * 4;
  for (const ox of [-9, 0, 9]) {
    const len = (ox === 0 ? fl * 1.25 : fl), w = ox === 0 ? 5 : 3.5;
    const g = ctx.createLinearGradient(0, 14, 0, 20 + len);
    g.addColorStop(0, '#fff'); g.addColorStop(0.35, P.flame); g.addColorStop(1, 'rgba(40,100,255,0)');
    ctx.fillStyle = g; ctx.beginPath(); ctx.moveTo(ox - w, 14); ctx.lineTo(ox, 20 + len); ctx.lineTo(ox + w, 14); ctx.closePath(); ctx.fill();
  }
  for (const s of [-1, 1]) {
    // asa externa
    ctx.fillStyle = P.wingD;
    ctx.beginPath(); ctx.moveTo(s * 8, -2); ctx.lineTo(s * 36, -10); ctx.lineTo(s * 40, 10); ctx.lineTo(s * 30, 20); ctx.lineTo(s * 10, 14); ctx.closePath(); ctx.fill();
    ctx.fillStyle = P.wing;
    ctx.beginPath(); ctx.moveTo(s * 8, -4); ctx.lineTo(s * 34, -12); ctx.lineTo(s * 37, 4); ctx.lineTo(s * 12, 8); ctx.closePath(); ctx.fill();
    ctx.fillStyle = 'rgba(255,255,255,.55)';
    ctx.beginPath(); ctx.moveTo(s * 12, -3); ctx.lineTo(s * 33, -11); ctx.lineTo(s * 34, -8); ctx.lineTo(s * 14, 0); ctx.closePath(); ctx.fill();
    // canhão lateral
    ctx.fillStyle = '#c8d4e8'; ctx.fillRect(s * 22 - 2, -22, 4, 20);
    ctx.fillStyle = P.wingD; ctx.fillRect(s * 22 - 3, -6, 6, 10);
    ctx.fillStyle = '#00e5ff'; ctx.fillRect(s * 22 - 1, -24, 2, 3);
    if (pw >= 5) { ctx.fillStyle = '#c8d4e8'; ctx.fillRect(s * 31 - 1.5, -16, 3, 14); ctx.fillStyle = '#ffb300'; ctx.fillRect(s * 31 - 1, -18, 2, 3); }
    if (pw >= 9) { ctx.fillStyle = '#c8d4e8'; ctx.fillRect(s * 14 - 1.5, -26, 3, 14); ctx.fillStyle = '#ff5a1f'; ctx.fillRect(s * 14 - 1, -28, 2, 3); }
    // luz de ponta de asa
    glow(GL_O, s * 38, 6, 12, 12, 0.9);
  }
  // fuselagem
  const hg = ctx.createLinearGradient(-12, 0, 12, 0);
  hg.addColorStop(0, P.hullD); hg.addColorStop(0.5, P.hull); hg.addColorStop(1, P.hullD);
  ctx.fillStyle = hg;
  ctx.beginPath(); ctx.moveTo(0, -32); ctx.lineTo(8, -12); ctx.lineTo(12, 8); ctx.lineTo(9, 18); ctx.lineTo(-9, 18); ctx.lineTo(-12, 8); ctx.lineTo(-8, -12); ctx.closePath(); ctx.fill();
  ctx.strokeStyle = 'rgba(255,255,255,.5)'; ctx.lineWidth = 1; ctx.stroke();
  ctx.fillStyle = P.wing;                                      // faixa central laranja
  ctx.beginPath(); ctx.moveTo(0, -4); ctx.lineTo(6, 6); ctx.lineTo(0, 14); ctx.lineTo(-6, 6); ctx.closePath(); ctx.fill();
  const cg = ctx.createLinearGradient(0, -22, 0, -2);          // cabine
  cg.addColorStop(0, '#e8ffff'); cg.addColorStop(1, '#2a9ad8');
  ctx.fillStyle = cg; ctx.beginPath(); ctx.ellipse(0, -13, 4.5, 9, 0, 0, 7); ctx.fill();
  ctx.fillStyle = 'rgba(255,255,255,.8)'; ctx.beginPath(); ctx.ellipse(-1.2, -16, 1.2, 4, 0, 0, 7); ctx.fill();
  if (shield > 0 && (shield > 1 || Math.floor(T * 10) % 2)) {
    const sg = ctx.createLinearGradient(-40, -40, 40, 40);
    sg.addColorStop(0, '#35ffd0'); sg.addColorStop(0.5, '#37a0ff'); sg.addColorStop(1, '#9dff3a');
    ctx.strokeStyle = sg; ctx.lineWidth = 3; ctx.globalAlpha = 0.85;
    ctx.beginPath(); ctx.arc(0, 0, 40, 0, 7); ctx.stroke();
    ctx.setLineDash([6, 8]); ctx.lineDashOffset = -T * 40; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.arc(0, 0, 34, 0, 7); ctx.stroke(); ctx.setLineDash([]);
    ctx.globalAlpha = 0.12; ctx.fillStyle = '#5ff'; ctx.beginPath(); ctx.arc(0, 0, 40, 0, 7); ctx.fill(); ctx.globalAlpha = 1;
  }
  ctx.restore();
}

/* ---- aliens alados (substituem as galinhas) ---- */
function drawAlien(x, y, s, type, ph) {
  const A = AL[type] || AL[0];
  const fl = 0.72 + 0.28 * Math.sin(T * 10 + ph);              // batida de asas
  glow(A.gl, x, y, 54 * s, 54 * s, 0.55);
  ctx.save(); ctx.translate(x, y); ctx.scale(s, s);
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.scale(sd * fl, 1);
    // asa de cima
    let g = ctx.createLinearGradient(0, 0, 24, -12);
    g.addColorStop(0, A.w2); g.addColorStop(1, A.w1);
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.moveTo(4, -4); ctx.bezierCurveTo(10, -22, 22, -24, 25, -16); ctx.bezierCurveTo(26, -8, 20, 0, 6, 3); ctx.closePath(); ctx.fill();
    // asa de baixo
    ctx.fillStyle = A.w2;
    ctx.beginPath(); ctx.moveTo(5, 2); ctx.bezierCurveTo(16, 2, 22, 8, 19, 15); ctx.bezierCurveTo(13, 17, 7, 11, 4, 6); ctx.closePath(); ctx.fill();
    // nervuras
    ctx.strokeStyle = A.wv; ctx.globalAlpha = 0.7; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(6, -3); ctx.lineTo(22, -17); ctx.moveTo(6, -2); ctx.lineTo(23, -9); ctx.moveTo(6, 4); ctx.lineTo(17, 12); ctx.stroke();
    ctx.globalAlpha = 1; ctx.strokeStyle = A.w1; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.moveTo(4, -4); ctx.bezierCurveTo(10, -22, 22, -24, 25, -16); ctx.stroke();
    ctx.restore();
    // antena
    ctx.strokeStyle = A.b1; ctx.lineWidth = 1.4;
    ctx.beginPath(); ctx.moveTo(sd * 3, -10); ctx.quadraticCurveTo(sd * 8, -18, sd * 6, -22); ctx.stroke();
    ctx.fillStyle = A.eye; ctx.beginPath(); ctx.arc(sd * 6, -22, 1.6, 0, 7); ctx.fill();
  }
  // corpo
  const bg = ctx.createLinearGradient(-8, 0, 8, 0);
  bg.addColorStop(0, A.b2); bg.addColorStop(0.5, A.b1); bg.addColorStop(1, A.b2);
  ctx.fillStyle = bg;
  ctx.beginPath(); ctx.ellipse(0, 3, 7.5, 13, 0, 0, 7); ctx.fill();
  ctx.strokeStyle = A.b2; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(-6, 2); ctx.lineTo(6, 2); ctx.moveTo(-5.5, 7); ctx.lineTo(5.5, 7); ctx.moveTo(-4, 12); ctx.lineTo(4, 12); ctx.stroke();
  // cabeça + olhos
  ctx.fillStyle = A.b1; ctx.beginPath(); ctx.ellipse(0, -9, 7, 6, 0, 0, 7); ctx.fill();
  ctx.fillStyle = A.eye; ctx.beginPath(); ctx.ellipse(-3.2, -9.5, 2.6, 3.2, 0.3, 0, 7); ctx.ellipse(3.2, -9.5, 2.6, 3.2, -0.3, 0, 7); ctx.fill();
  ctx.fillStyle = '#220a00'; ctx.beginPath(); ctx.arc(-3.2, -9, 1.1, 0, 7); ctx.arc(3.2, -9, 1.1, 0, 7); ctx.fill();
  ctx.strokeStyle = A.b2; ctx.lineWidth = 1.3;                 // mandíbulas
  ctx.beginPath(); ctx.moveTo(-2, -4); ctx.lineTo(-1, -1); ctx.moveTo(2, -4); ctx.lineTo(1, -1); ctx.stroke();
  ctx.restore();
}

function drawBoss(x, y, hpPct) {
  const fl = 0.85 + 0.15 * Math.sin(T * 7), rage = hpPct < 0.35;
  glow(rage ? GL_R : GL_O, x, y, 200, 170, 0.7);
  ctx.save(); ctx.translate(x, y + 6); ctx.scale(0.78, 0.78);
  for (const sd of [-1, 1]) {
    ctx.save(); ctx.scale(sd * fl, 1);
    let g = ctx.createLinearGradient(10, 0, 100, -40);
    g.addColorStop(0, '#7a1a08'); g.addColorStop(0.6, '#ff6a1a'); g.addColorStop(1, '#ffd54a');
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.moveTo(14, -16); ctx.bezierCurveTo(40, -70, 90, -74, 104, -48); ctx.bezierCurveTo(100, -20, 70, 0, 18, 8); ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#5a1a8a';
    ctx.beginPath(); ctx.moveTo(16, 6); ctx.bezierCurveTo(50, 4, 86, 18, 84, 42); ctx.bezierCurveTo(60, 50, 28, 34, 14, 18); ctx.closePath(); ctx.fill();
    ctx.strokeStyle = '#ffe9a0'; ctx.globalAlpha = 0.7; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(20, -12); ctx.lineTo(96, -46); ctx.moveTo(20, -6); ctx.lineTo(98, -30); ctx.moveTo(20, 12); ctx.lineTo(78, 36); ctx.stroke();
    ctx.globalAlpha = 1;
    ctx.fillStyle = '#c8d4e8'; ctx.fillRect(40, -4, 5, 26); glow(GL_R, 42, 24, 22, 22, 0.9);   // canhões
    ctx.restore();
  }
  const bg = ctx.createLinearGradient(-26, 0, 26, 0);
  bg.addColorStop(0, '#4a1408'); bg.addColorStop(0.5, '#ff9a2a'); bg.addColorStop(1, '#4a1408');
  ctx.fillStyle = bg; ctx.beginPath(); ctx.ellipse(0, 6, 26, 44, 0, 0, 7); ctx.fill();
  ctx.strokeStyle = '#3a0c04'; ctx.lineWidth = 2;
  for (let i = 0; i < 4; i++) { ctx.beginPath(); ctx.moveTo(-22 + i * 2, -8 + i * 14); ctx.lineTo(22 - i * 2, -8 + i * 14); ctx.stroke(); }
  const core = 0.6 + 0.4 * Math.sin(T * 6);                   // núcleo pulsante
  glow(rage ? GL_R : GL_C, 0, 14, 44, 44, core);
  ctx.fillStyle = rage ? '#ff4030' : '#aef3ff'; ctx.beginPath(); ctx.arc(0, 14, 7, 0, 7); ctx.fill();
  ctx.fillStyle = '#ff9a2a'; ctx.beginPath(); ctx.ellipse(0, -38, 20, 15, 0, 0, 7); ctx.fill();
  ctx.fillStyle = '#ffeb7a';
  ctx.beginPath(); ctx.ellipse(-8, -40, 6, 8, 0.35, 0, 7); ctx.ellipse(8, -40, 6, 8, -0.35, 0, 7); ctx.fill();
  ctx.fillStyle = rage ? '#ff1a1a' : '#2a0a00';
  ctx.beginPath(); ctx.arc(-8, -39, 2.6, 0, 7); ctx.arc(8, -39, 2.6, 0, 7); ctx.fill();
  ctx.strokeStyle = '#ffd54a'; ctx.lineWidth = 3;               // chifres/antenas
  ctx.beginPath(); ctx.moveTo(-12, -50); ctx.quadraticCurveTo(-30, -70, -24, -90); ctx.moveTo(12, -50); ctx.quadraticCurveTo(30, -70, 24, -90); ctx.stroke();
  ctx.strokeStyle = '#3a0c04'; ctx.lineWidth = 3;               // mandíbulas
  ctx.beginPath(); ctx.moveTo(-8, -26); ctx.lineTo(-4, -16); ctx.moveTo(8, -26); ctx.lineTo(4, -16); ctx.stroke();
  ctx.restore();
}

/* ---- tiros ---- */
function drawBulletShape(x, y, vx) {
  const ang = Math.atan2(vx || 0, 560);                         // inclina com a trajetória
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
  let g = ctx.createLinearGradient(0, -18, 0, 16);
  g.addColorStop(0, 'rgba(120,200,255,0)'); g.addColorStop(0.25, '#2a8cff'); g.addColorStop(1, 'rgba(30,80,255,0)');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.moveTo(0, -18); ctx.bezierCurveTo(5, -8, 4.5, 8, 0, 18); ctx.bezierCurveTo(-4.5, 8, -5, -8, 0, -18); ctx.fill();
  ctx.fillStyle = '#e6fcff';
  ctx.beginPath(); ctx.moveTo(0, -13); ctx.bezierCurveTo(2.2, -6, 2, 4, 0, 9); ctx.bezierCurveTo(-2, 4, -2.2, -6, 0, -13); ctx.fill();
  ctx.restore();
}

function bolt(x, y, s) {
  ctx.fillStyle = '#fff'; ctx.beginPath();
  ctx.moveTo(x + 2 * s, y - 8 * s); ctx.lineTo(x - 5 * s, y + 1 * s); ctx.lineTo(x - 0.5 * s, y + 1 * s);
  ctx.lineTo(x - 2 * s, y + 8 * s); ctx.lineTo(x + 5 * s, y - 2 * s); ctx.lineTo(x + 0.5 * s, y - 2 * s);
  ctx.closePath(); ctx.fill();
}

function drawEnemyShot(x, y, vx, vy) {                          // laser/plasma vermelho
  const ang = Math.atan2(vy, vx) - Math.PI / 2, boss = Math.abs(vx) > 20;
  glow(boss ? GL_M : GL_R, x, y, 34, 34, 0.8);
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
  let g = ctx.createLinearGradient(0, -16, 0, 12);
  g.addColorStop(0, 'rgba(255,60,40,0)'); g.addColorStop(0.5, boss ? '#ff3fd0' : '#ff3b2a'); g.addColorStop(1, '#ffb347');
  ctx.fillStyle = g;
  ctx.beginPath(); ctx.moveTo(0, -16); ctx.bezierCurveTo(4.5, -4, 4.5, 8, 0, 12); ctx.bezierCurveTo(-4.5, 8, -4.5, -4, 0, -16); ctx.fill();
  ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(0, 6, 2.6, 0, 7); ctx.fill();
  ctx.restore();
}

function drawDrop(d, ex) {
  const y = d.y + d.vy * ex;
  ctx.save(); ctx.translate(d.x, y);
  if (d.k === 0) {
    glow(GL_O, 0, 0, 32, 32, 0.75);
    ctx.scale(Math.max(0.15, Math.abs(Math.cos(T * 4 + d.x))), 1);
    ctx.fillStyle = '#ffd54a'; ctx.beginPath(); ctx.arc(0, 0, 9, 0, 7); ctx.fill();
    ctx.strokeStyle = '#c98a12'; ctx.lineWidth = 1.5; ctx.stroke();
    ctx.fillStyle = '#8a5a00'; ctx.font = 'bold 12px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('$', 0, 1);
  } else {                                                      // cápsula de energia laranja
    glow(GL_O, 0, 0, 46, 46, 0.95);
    ctx.rotate(Math.sin(T * 3 + d.x) * 0.25);
    const g = ctx.createLinearGradient(0, -12, 0, 12);
    g.addColorStop(0, '#ffe08a'); g.addColorStop(0.5, '#ff8a1f'); g.addColorStop(1, '#a8400a');
    ctx.fillStyle = g; ctx.beginPath();
    ctx.moveTo(0, -13); ctx.lineTo(9, -4); ctx.lineTo(9, 7); ctx.lineTo(0, 13); ctx.lineTo(-9, 7); ctx.lineTo(-9, -4); ctx.closePath(); ctx.fill();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.4; ctx.stroke();
    bolt(0, 0, 1);
  }
  ctx.restore();
}

/* ---- HUD tecnológico ---- */
function techPanel(x, y, w, h, c) {
  c = c || 7;
  ctx.beginPath();
  ctx.moveTo(x + c, y); ctx.lineTo(x + w, y); ctx.lineTo(x + w, y + h - c); ctx.lineTo(x + w - c, y + h);
  ctx.lineTo(x, y + h); ctx.lineTo(x, y + c); ctx.closePath();
  ctx.fillStyle = 'rgba(2,16,38,.75)'; ctx.fill();
  ctx.strokeStyle = 'rgba(0,229,255,.6)'; ctx.lineWidth = 1; ctx.stroke();
}
function hexIcon(x, y, col, glyph) {
  ctx.beginPath();
  for (let i = 0; i < 6; i++) { const a = Math.PI / 3 * i + Math.PI / 6; ctx[i ? 'lineTo' : 'moveTo'](x + Math.cos(a) * 10, y + Math.sin(a) * 10); }
  ctx.closePath(); ctx.fillStyle = col; ctx.fill();
  ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.lineWidth = 1.2; ctx.stroke();
  ctx.fillStyle = '#fff'; ctx.font = 'bold 11px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText(glyph, x, y + 1);
}
function miniShip(x, y, col) {
  ctx.fillStyle = col; ctx.beginPath();
  ctx.moveTo(x, y - 6); ctx.lineTo(x + 6, y + 5); ctx.lineTo(x, y + 2); ctx.lineTo(x - 6, y + 5); ctx.closePath(); ctx.fill();
}

function drawHUD(p) {
  ctx.textBaseline = 'middle';
  // painel esquerdo: moedas e pontos
  techPanel(6, H - 62, 124, 56);
  hexIcon(24, H - 46, '#c98a00', '$');
  hexIcon(24, H - 22, '#d9561a', '★');
  ctx.font = FH; ctx.textAlign = 'left';
  ctx.font = '700 14px Orbitron, sans-serif';
  ctx.fillStyle = '#ffd54a'; ctx.fillText(p.coins, 42, H - 46);
  ctx.fillStyle = '#ff9a2e'; ctx.fillText(p.score, 42, H - 22);

  // painel direito: nível e poder
  const rx = W - 6 - 140;
  techPanel(rx, H - 62, 140, 56);
  ctx.font = '700 11px Orbitron, sans-serif';
  ctx.textAlign = 'left'; ctx.fillStyle = '#4fc3ff'; ctx.fillText('NÍVEL ' + V.level, rx + 10, H - 48);
  ctx.textAlign = 'right'; ctx.fillStyle = '#ffb300'; ctx.fillText('PWR ' + p.power + '/' + MAXP, rx + 130, H - 48);
  for (let i = 0; i < MAXP; i++) {
    ctx.fillStyle = i < p.power ? (i > 8 ? '#ff5a1f' : '#00e5ff') : 'rgba(0,229,255,.15)';
    ctx.fillRect(rx + 10 + i * 10, H - 34, 8, 14);
  }

  // vidas
  ctx.textAlign = 'left'; ctx.font = '700 10px Orbitron, sans-serif';
  V.players.forEach((q, i) => {
    const label = V.players.length > 1 ? (i === myIdx ? 'VOCÊ' : 'AMIGO') : 'VIDAS';
    const y = 16 + i * 18;
    ctx.fillStyle = PAL[i].tag; ctx.fillText(label, 8, y);
    for (let l = 0; l < Math.min(5, Math.max(0, q.lives)); l++) miniShip(60 + l * 15, y, PAL[i].tag);
  });

  // rede
  if (mode !== 'local') {
    ctx.textAlign = 'right';
    const ok = mode === 'host' || (netPing && netPing < 150);
    ctx.fillStyle = mode === 'guest' && netPing > 250 ? '#ff4d6a' : ok ? '#7dffc4' : '#ffd54a';
    ctx.fillText('● ' + (mode === 'guest' ? (netPing ? Math.round(netPing) + 'ms' : '...') : 'HOST'), W - 124, 16);
  }
}

function render(dt, now) {
  ctx.setTransform(K, 0, 0, K, 0, 0);
  drawBackground(dt);
  if (!V) {
    ctx.fillStyle = '#9fe9ff'; ctx.font = '700 16px Orbitron, sans-serif'; ctx.textAlign = 'center';
    ctx.fillText('CONECTANDO…', W / 2, H / 2);
    return;
  }
  const ex = mode === 'guest' ? clamp((now - snapT) / 1000, 0, 0.1) : 0;   // extrapolação (guest)

  if (V.level !== lastLevel) {
    lastLevel = V.level; bannerT = 2.2;
    bannerTxt = V.level % 5 === 0 ? 'BOSS!' : 'NÍVEL ' + V.level;
  }

  for (const d of V.drops) drawDrop(d, ex);
  for (const g of V.eggs) drawEnemyShot(g.x + (g.vx || 0) * ex, g.y + (g.vy || 0) * ex, g.vx || 0, g.vy || 150);
  let boss = null;
  for (const e of V.enemies) {
    if (e.boss) { boss = e; drawBoss(e.x, e.y, e.hp / e.maxhp); }
    else drawAlien(e.x, e.y, 0.9, e.type, e.x * 0.05);
  }
  // tiros (brilho + forma)
  for (const b of V.bullets) glow(GL_B, b.x + (b.vx || 0) * ex, b.y - 560 * ex, 26, 54, 0.8);
  for (const b of V.bullets) drawBulletShape(b.x + (b.vx || 0) * ex, b.y - 560 * ex, b.vx);

  V.players.forEach((p, i) => {
    if (!p.alive) return;
    let x = p.x, y = p.y;
    if (mode === 'guest') {
      if (i === myIdx) { x = me.x; y = me.y; }
      else {
        const r = rp[i] || (rp[i] = { x: p.x, y: p.y }), k = Math.min(1, dt * 16);
        r.x += (p.x - r.x) * k; r.y += (p.y - r.y) * k; x = r.x; y = r.y;
      }
    }
    drawShip(x, y, i, p.shield, p.power);
  });

  ctx.globalCompositeOperation = 'lighter';
  for (let i = rings.length - 1; i >= 0; i--) {
    const q = rings[i]; q.life -= dt;
    if (q.life <= 0) { rings.splice(i, 1); continue; }
    const k = 1 - q.life / q.max;
    ctx.globalAlpha = (1 - k) * 0.85; ctx.strokeStyle = q.c; ctx.lineWidth = 3 * (1 - k) + 1;
    ctx.beginPath(); ctx.arc(q.x, q.y, q.r * (0.15 + k), 0, 7); ctx.stroke();
    if (k < 0.3) { ctx.globalAlpha = (0.3 - k) * 2.2; glow(GL_O, q.x, q.y, q.r * 1.6, q.r * 1.6, 1); ctx.globalCompositeOperation = 'lighter'; }
  }
  for (let i = parts.length - 1; i >= 0; i--) {
    const p = parts[i];
    p.life -= dt; if (p.life <= 0) { parts.splice(i, 1); continue; }
    p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 0.96; p.vy *= 0.96;
    ctx.globalAlpha = Math.max(0, p.life / p.max);
    ctx.fillStyle = p.c; ctx.beginPath(); ctx.arc(p.x, p.y, p.r, 0, 7); ctx.fill();
  }
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';

  if (boss) {
    const bx = W / 2 - 80, by = 52;
    ctx.fillStyle = 'rgba(0,0,0,.55)'; ctx.fillRect(bx - 2, by - 2, 164, 12);
    const fw = 160 * clamp(boss.hp / boss.maxhp, 0, 1);
    const gr = ctx.createLinearGradient(bx, 0, bx + 160, 0); gr.addColorStop(0, '#ff2bd6'); gr.addColorStop(1, '#ff3b30');
    ctx.fillStyle = gr; ctx.fillRect(bx, by, fw, 8);
    ctx.strokeStyle = 'rgba(255,255,255,.35)'; ctx.lineWidth = 1; ctx.beginPath();
    for (let i = 1; i < 10; i++) { ctx.moveTo(bx + i * 16, by); ctx.lineTo(bx + i * 16, by + 8); }
    ctx.stroke();
    ctx.fillStyle = '#ff8da0'; ctx.font = '700 9px Orbitron, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText('CHEFE', W / 2, by + 20);
  }

  const mp = V.players[myIdx] || V.players[0];
  drawHUD(mp);

  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  if (V.state === 'clear') {
    ctx.font = '900 24px Orbitron, sans-serif';
    ctx.fillStyle = '#7dffc4'; ctx.shadowColor = '#2fe08a'; ctx.shadowBlur = 14;
    ctx.fillText('ONDA ELIMINADA', W / 2, H / 2 - 40);
    ctx.shadowBlur = 0;
  } else if (bannerT > 0 && V.state === 'play') {
    bannerT -= dt;
    ctx.globalAlpha = clamp(bannerT, 0, 1);
    ctx.font = '900 36px Orbitron, sans-serif';
    ctx.fillStyle = bannerTxt === 'BOSS!' ? '#ff4d6a' : '#00e5ff';
    ctx.shadowColor = ctx.fillStyle; ctx.shadowBlur = 16;
    ctx.fillText(bannerTxt, W / 2, H / 2 - 60);
    ctx.shadowBlur = 0; ctx.globalAlpha = 1;
  }

  if (V.state === 'over' && !overShown) showOver();
}

/* ============================ FIM DE JOGO ============================== */
function showOver() {
  overShown = true;
  const p = V.players[myIdx] || V.players[0];
  if (p.score > best) { best = p.score; try { localStorage.setItem('gxs_best', best); } catch (e) {} }
  $('overScore').textContent = p.score;
  $('overBest').textContent = best;
  $('overTeam').innerHTML = V.players.length > 1
    ? V.players.map((q, i) => '<li>' + (i === myIdx ? 'Você' : 'Amigo') + ': ' + q.score + ' pts • 💰 ' + q.coins + '</li>').join('')
    : '<li>Moedas: ' + p.coins + ' • Nível ' + V.level + '</li>';
  const guest = mode === 'guest';
  $('btnAgain').style.display = guest ? 'none' : '';
  netMsg('overWait', guest ? 'Aguardando o anfitrião reiniciar…' : '', true);
  $('over').classList.add('show');
}

/* ============================ BOTÕES / UI ============================== */
$('btnLocal').onclick = startLocal;
$('btnOnline').onclick = () => { netMsg('onlineMsg', ''); show('online'); };
$('btnBackOnline').onclick = () => show('menu');
$('btnCreate').onclick = () => createRoom();
$('btnJoin').onclick = () => joinRoom($('roomInput').value);
$('roomInput').addEventListener('keydown', e => { if (e.key === 'Enter') joinRoom($('roomInput').value); });
$('roomInput').addEventListener('input', e => { e.target.value = e.target.value.toUpperCase().replace(/[^A-Z0-9]/g, ''); });
$('btnStartOnline').onclick = startHost;
$('btnLeaveLobby').onclick = leaveToMenu;
$('btnExit').onclick = leaveToMenu;
$('btnOverMenu').onclick = leaveToMenu;
$('btnAgain').onclick = () => { if (mode === 'local') startLocal(); else if (mode === 'host') startHost(); };
$('btnSound').onclick = () => { muted = !muted; $('btnSound').textContent = muted ? '🔇' : '🔊'; };

const fsEl = document.documentElement;
const fsReq = fsEl.requestFullscreen || fsEl.webkitRequestFullscreen;
if (!fsReq) $('btnFull').style.display = 'none';          // ex.: iPhone não suporta
$('btnFull').onclick = () => {
  try {
    if (document.fullscreenElement || document.webkitFullscreenElement) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
    else fsReq.call(fsEl);
  } catch (e) {}
};

function roomLink() { return location.origin + location.pathname + '?sala=' + net.code; }
function copyText(txt, okMsg) {
  const done = () => toast(okMsg);
  if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(txt).then(done, () => toast(txt));
  else toast(txt);
}
$('btnCopyCode').onclick = () => copyText(net.code, 'Código copiado!');
$('btnCopyLink').onclick = () => copyText(roomLink(), 'Link copiado!');
if (!navigator.share) $('btnShare').style.display = 'none';
$('btnShare').onclick = () => {
  navigator.share({ title: 'Galaxy Strike', text: 'Entre na minha sala do Galaxy Strike! Código: ' + net.code, url: roomLink() }).catch(() => {});
};

/* entrar direto por link: ?sala=ABCDE */
(function () {
  const c = new URLSearchParams(location.search).get('sala');
  if (c) { $('roomInput').value = c.toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 5); show('online'); }
})();
fit();
