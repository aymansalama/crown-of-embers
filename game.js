'use strict';
(() => {
// ---------------------------------------------------------------------------
// Constants & helpers
// ---------------------------------------------------------------------------
const W = 1500, H = 1100;          // world size
const RES = 2, GW = W / RES, GH = H / RES; // simulation grid
const BS = 2;                       // baked base-map scale
const TAU = Math.PI * 2;
const $ = id => document.getElementById(id);

const cv = $('map'), ctx = cv.getContext('2d');

function mulberry32(a) {
  return () => {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
let rand = Math.random;
const rr = (a, b) => a + (b - a) * rand();
const ri = (a, b) => Math.floor(rr(a, b + 1));
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;
const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const hexRGB = h => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];
const rgba = (c, a) => `rgba(${c[0]|0},${c[1]|0},${c[2]|0},${a})`;
const sleep = ms => new Promise(r => setTimeout(r, ms));

// Value noise
const perm = new Uint8Array(512);
function seedNoise() {
  const p = new Uint8Array(256);
  for (let i = 0; i < 256; i++) p[i] = i;
  for (let i = 255; i > 0; i--) { const j = Math.floor(rand() * (i + 1)); const t = p[i]; p[i] = p[j]; p[j] = t; }
  for (let i = 0; i < 512; i++) perm[i] = p[i & 255];
}
const hash = (x, y) => perm[perm[x & 255] + (y & 255)] / 255;
function vnoise(x, y) {
  const xi = Math.floor(x), yi = Math.floor(y), xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf);
  const a = hash(xi, yi), b = hash(xi + 1, yi), c = hash(xi, yi + 1), d = hash(xi + 1, yi + 1);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
function fbm(x, y, o) {
  let s = 0, a = .5, f = 1, n = 0;
  for (let i = 0; i < o; i++) { s += a * vnoise(x * f, y * f); n += a; a *= .5; f *= 2.07; }
  return s / n;
}

// ---------------------------------------------------------------------------
// Houses
// ---------------------------------------------------------------------------
const HOUSES = [
  { name: 'Aurelion', words: 'Dawn Breaks All', field: '#8e1b1b', field2: '#4a0b0b', charge: '#f1c14e', map: '#d8372a', emblem: 'sun',
    atk: 1, def: 1, gold: 1.25, trait: '+25% gold from holdings' },
  { name: 'Morvayne', words: 'The Night Remembers', field: '#2a2f6e', field2: '#12143a', charge: '#dfe4f0', map: '#6f73ea', emblem: 'moon',
    atk: 1.1, def: 1.1, gold: 1, trait: '+10% attack and defence' },
  { name: 'Thornwick', words: 'Rooted, Unbroken', field: '#2d5d31', field2: '#132a15', charge: '#ece1c4', map: '#4cb352', emblem: 'tower',
    atk: 1, def: 1.25, gold: 1, trait: '+25% defence' },
  { name: 'Ashgrave', words: 'From Ash, Fire', field: '#221e1e', field2: '#080707', charge: '#f2801f', map: '#f0902a', emblem: 'flame',
    atk: 1.2, def: 1, gold: 1, trait: '+20% attack' },
  { name: 'Valsmere', words: 'By Star and Tide', field: '#1c666b', field2: '#0a3135', charge: '#f4f2e6', map: '#35c9c1', emblem: 'star',
    atk: 1, def: 1, gold: 1.1, sea: true, trait: 'Sea crossings without penalty, +10% gold' },
];
HOUSES.forEach(h => { h.rgb = hexRGB(h.map); });
const SEASONS = [
  { name: 'Spring', sub: 'The roads thaw. The banners stir.' },
  { name: 'Summer', sub: 'Long days and full granaries.' },
  { name: 'Autumn', sub: 'The leaves turn red. So do the rivers.' },
  { name: 'Winter', sub: 'Harvests fail. The cold bleeds every host.' },
];

// ---------------------------------------------------------------------------
// World state
// ---------------------------------------------------------------------------
const height = new Float32Array(GW * GH);
const moist = new Float32Array(GW * GH);
const regionOf = new Int16Array(GW * GH);
const regionBorder = new Uint8Array(GW * GH);
const ownGrid = new Int8Array(GW * GH);
const distGrid = new Uint8Array(GW * GH);
const bfsQ = new Int32Array(GW * GH);
let regions = [], seaLinks = [], throneId = 0;
let glints = [], clouds = [], seaLabels = [];
const baseCv = document.createElement('canvas');
const ovCv = document.createElement('canvas');
ovCv.width = GW; ovCv.height = GH;
const ovCtx = ovCv.getContext('2d');
const ovImg = ovCtx.createImageData(GW, GH);

const hAt = (x, y) => height[clamp(y / RES | 0, 0, GH - 1) * GW + clamp(x / RES | 0, 0, GW - 1)];

// ---------------------------------------------------------------------------
// Terrain generation
// ---------------------------------------------------------------------------
function genHeight() {
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx, nx = gx / GW, ny = gy / GH;
    const wx = nx + (fbm(nx * 3 + 5, ny * 3 + 5, 3) - .5) * .35;
    const wy = ny + (fbm(nx * 3 + 15, ny * 3 + 25, 3) - .5) * .35;
    const dx = (wx - .5) / .40, dy = (wy - .5) / .45;
    const d = Math.sqrt(dx * dx + dy * dy);
    let h = .5 - d * .58 + (fbm(nx * 5 * 1.36, ny * 5, 6) - .5) * .8;
    if (h > 0) {
      const r = 1 - Math.abs(fbm(nx * 6 * 1.36 + 40, ny * 6 + 40, 5) * 2 - 1);
      h = h * .4 + Math.pow(r, 6) * .62 * smooth(0, .12, h);
    }
    height[i] = h;
    moist[i] = fbm(nx * 5 + 80, ny * 5 + 80, 4);
  }
}

const BIOME = [
  [0, [236, 239, 242]], [.11, [205, 212, 212]], [.2, [132, 146, 128]], [.3, [70, 98, 70]],
  [.48, [98, 130, 70]], [.64, [140, 148, 82]], [.78, [184, 160, 98]], [1, [214, 182, 122]],
];
function biome(t) {
  t = clamp(t, 0, 1);
  for (let k = 1; k < BIOME.length; k++) if (t <= BIOME[k][0]) {
    const [t0, c0] = BIOME[k - 1], [t1, c1] = BIOME[k], f = smooth(0, 1, (t - t0) / (t1 - t0));
    return [lerp(c0[0], c1[0], f), lerp(c0[1], c1[1], f), lerp(c0[2], c1[2], f)];
  }
  return BIOME[BIOME.length - 1][1];
}
const latOf = (gx, gy, i) => gy / GH + (moist[i] - .5) * .18;
const snowLine = lat => .42 + lat * .3;

function terrainImage() {
  const tc = document.createElement('canvas'); tc.width = GW; tc.height = GH;
  const tctx = tc.getContext('2d'); const img = tctx.createImageData(GW, GH); const d = img.data;
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx, h = height[i];
    let r, g, b;
    const hl = height[i - (gx > 0 ? 1 : 0)], hr = height[i + (gx < GW - 1 ? 1 : 0)];
    const hu = height[i - (gy > 0 ? GW : 0)], hd = height[i + (gy < GH - 1 ? GW : 0)];
    if (h > 0) {
      const lat = latOf(gx, gy, i);
      let c = biome(lat);
      // forests darken
      const forest = smooth(.5, .66, moist[i]) * smooth(.12, .25, lat) * (1 - smooth(.72, .85, lat));
      c = [c[0] * (1 - .32 * forest), c[1] * (1 - .2 * forest), c[2] * (1 - .3 * forest)];
      // beaches
      const beach = (1 - smooth(.0, .025, h)) * smooth(.25, .5, lat);
      c = [lerp(c[0], 218, beach), lerp(c[1], 200, beach), lerp(c[2], 152, beach)];
      // rock & snow
      const rock = smooth(.34, .56, h);
      c = [lerp(c[0], 128, rock), lerp(c[1], 118, rock), lerp(c[2], 106, rock)];
      const sl = snowLine(lat), snow = smooth(sl, sl + .07, h);
      c = [lerp(c[0], 244, snow), lerp(c[1], 246, snow), lerp(c[2], 250, snow)];
      // hillshade
      const sx = (hr - hl), sy = (hd - hu);
      const shade = clamp(1 + (-sx * .8 - sy * 1.0) * 26, .5, 1.45);
      r = c[0] * shade; g = c[1] * shade; b = c[2] * shade;
      // coast outline
      if (hl <= 0 || hr <= 0 || hu <= 0 || hd <= 0) { r *= .45; g *= .42; b *= .38; }
    } else {
      const dep = -h;
      const f = smooth(0, .28, dep);
      r = lerp(84, 10, f); g = lerp(150, 30, f); b = lerp(158, 52, f);
      // old-map contour ripples near the shore
      if (dep < .09) {
        const band = (dep * 60) % 1;
        const k = (band < .22 ? .32 : 0) * (1 - dep / .09);
        r = lerp(r, 210, k); g = lerp(g, 226, k); b = lerp(b, 214, k);
      }
      if (hl > 0 || hr > 0 || hu > 0 || hd > 0) { r = lerp(r, 230, .5); g = lerp(g, 236, .5); b = lerp(b, 222, .5); }
      const n = vnoise(gx * .05, gy * .05) - .5;
      r += n * 14; g += n * 18; b += n * 20;
    }
    // warm, painterly grade + grain
    const lum = (r + g + b) / 3;
    r = lerp(r, lum * 1.1, .08); g = lerp(g, lum * 1.0, .08); b = lerp(b, lum * .82, .08);
    const gr = (rand() - .5) * 7;
    const o = i * 4;
    d[o] = clamp(r + gr, 0, 255); d[o + 1] = clamp(g + gr, 0, 255); d[o + 2] = clamp(b + gr, 0, 255); d[o + 3] = 255;
  }
  tctx.putImageData(img, 0, 0);
  return tc;
}

function traceRivers() {
  const rivers = [];
  for (let k = 0; k < 160 && rivers.length < 9; k++) {
    let gx = ri(5, GW - 6), gy = ri(5, GH - 6);
    let i = gy * GW + gx;
    if (height[i] < .3 || height[i] > .5) continue;
    const pts = [], seen = new Set();
    let ok = false;
    for (let s = 0; s < 900; s++) {
      pts.push([gx * RES, gy * RES]); seen.add(i);
      if (height[i] <= 0) { ok = true; break; }
      let best = -1, bh = 1e9;
      for (let dy = -2; dy <= 2; dy++) for (let dx = -2; dx <= 2; dx++) {
        if (!dx && !dy) continue;
        const nx = gx + dx, ny = gy + dy;
        if (nx < 1 || ny < 1 || nx >= GW - 1 || ny >= GH - 1) continue;
        const n = ny * GW + nx;
        if (seen.has(n)) continue;
        const hh = height[n] + rand() * .004;
        if (hh < bh) { bh = hh; best = n; }
      }
      if (best < 0) break;
      i = best; gx = i % GW; gy = (i / GW) | 0;
    }
    if (ok && pts.length > 60) rivers.push(pts.filter((_, j) => j % 3 === 0 || j === pts.length - 1));
  }
  return rivers;
}

function drawMountain(c, x, y, s, snowy) {
  c.fillStyle = 'rgba(30,22,14,.28)';
  c.beginPath(); c.ellipse(x + s * .35, y + 1, s * 1.1, s * .3, 0, 0, TAU); c.fill();
  const px = x - s * .12, py = y - s * 1.15;
  c.fillStyle = '#a79d8b';
  c.beginPath(); c.moveTo(x - s, y); c.lineTo(px, py); c.lineTo(x + s * .12, y); c.closePath(); c.fill();
  c.fillStyle = '#5f564a';
  c.beginPath(); c.moveTo(px, py); c.lineTo(x + s, y); c.lineTo(x + s * .12, y); c.closePath(); c.fill();
  if (snowy) {
    c.fillStyle = '#f6f7fa';
    c.beginPath(); c.moveTo(px, py); c.lineTo(px - s * .38, py + s * .42); c.lineTo(px - s * .1, py + s * .32);
    c.lineTo(px + s * .05, py + s * .48); c.lineTo(px + s * .2, py + s * .3); c.lineTo(px + s * .36, py + s * .4); c.closePath(); c.fill();
  }
  c.strokeStyle = 'rgba(40,30,20,.7)'; c.lineWidth = .7;
  c.beginPath(); c.moveTo(x - s, y); c.lineTo(px, py); c.lineTo(x + s, y); c.stroke();
}
function drawTree(c, x, y, s, conifer, tint) {
  c.fillStyle = 'rgba(20,24,12,.3)';
  c.beginPath(); c.ellipse(x + s * .3, y + .5, s * .8, s * .3, 0, 0, TAU); c.fill();
  if (conifer) {
    c.fillStyle = tint ? '#2b4636' : '#2c4a30';
    c.beginPath(); c.moveTo(x, y - s * 2.1); c.lineTo(x + s * .8, y); c.lineTo(x - s * .8, y); c.closePath(); c.fill();
    c.fillStyle = tint ? '#47685a' : '#4a6e44';
    c.beginPath(); c.moveTo(x, y - s * 2.1); c.lineTo(x - s * .8, y); c.lineTo(x - s * .1, y); c.closePath(); c.fill();
  } else {
    c.fillStyle = '#3d5a2a';
    c.beginPath(); c.arc(x, y - s * .9, s * .9, 0, TAU); c.fill();
    c.fillStyle = '#6a8a40';
    c.beginPath(); c.arc(x - s * .3, y - s * 1.15, s * .45, 0, TAU); c.fill();
  }
}

function bakeBase() {
  baseCv.width = W * BS; baseCv.height = H * BS;
  const c = baseCv.getContext('2d');
  c.imageSmoothingEnabled = true; c.imageSmoothingQuality = 'high';
  c.drawImage(terrainImage(), 0, 0, W * BS, H * BS);
  c.save(); c.scale(BS, BS);

  // rivers
  for (const pts of traceRivers()) {
    for (const [lw, col] of [[3.2, 'rgba(40,60,60,.5)'], [1.9, '#5d9db0']]) {
      c.strokeStyle = col; c.lineCap = 'round'; c.lineJoin = 'round';
      for (let j = 1; j < pts.length; j++) {
        c.lineWidth = lw * (.35 + .65 * j / pts.length);
        c.beginPath();
        const [x0, y0] = pts[j - 1], [x1, y1] = pts[j];
        c.moveTo(x0, y0); c.lineTo(x1, y1); c.stroke();
      }
    }
  }

  // decorations: mountains & forests, sorted by y for overlap
  const deco = [];
  for (let y = 4; y < H - 4; y += 7) for (let x = 4; x < W - 4; x += 7) {
    const jx = x + rr(-3, 3), jy = y + rr(-3, 3);
    const gx = jx / RES | 0, gy = jy / RES | 0, i = gy * GW + gx, h = height[i];
    if (h <= .02) continue;
    const lat = latOf(gx, gy, i);
    if (h > .4 && rand() < smooth(.4, .62, h) * .3) {
      deco.push({ t: 'm', x: jx, y: jy, s: 7 + (h - .36) * 40 + rr(0, 3), snow: h > snowLine(lat) - .04 });
    } else if (h < .34) {
      const forest = smooth(.52, .64, moist[i]) * smooth(.14, .24, lat) * (1 - smooth(.7, .8, lat));
      if (rand() < forest * .9) deco.push({ t: 't', x: jx, y: jy, s: rr(2.2, 3.4), con: lat < .42, tint: lat < .26 });
      else if (h > .2 && rand() < .12) deco.push({ t: 'h', x: jx, y: jy, s: rr(5, 8) });
    }
  }
  deco.sort((a, b) => a.y - b.y);
  for (const d of deco) {
    if (d.t === 'm') drawMountain(c, d.x, d.y, d.s, d.snow);
    else if (d.t === 't') drawTree(c, d.x, d.y, d.s, d.con, d.tint);
    else {
      c.strokeStyle = 'rgba(50,40,25,.45)'; c.lineWidth = .8;
      c.beginPath(); c.arc(d.x, d.y + d.s * .6, d.s, Math.PI * 1.15, Math.PI * 1.85); c.stroke();
    }
  }

  // sea labels
  for (const s of seaLabels) {
    c.save(); c.translate(s.x, s.y); c.rotate(s.rot);
    c.font = `italic 500 ${s.size}px "Cormorant Garamond", Georgia, serif`;
    c.textAlign = 'center'; c.fillStyle = 'rgba(200,220,215,.55)';
    if (c.letterSpacing !== undefined) c.letterSpacing = '6px';
    c.fillText(s.text, 0, 0);
    c.restore();
  }
  drawCompass(c, W - 95, H - 95, 55);

  c.restore();

  // paper grain
  const g = document.createElement('canvas'); g.width = g.height = 256;
  const gc = g.getContext('2d'), gi = gc.createImageData(256, 256);
  for (let k = 0; k < gi.data.length; k += 4) { const v = rand() * 255; gi.data[k] = gi.data[k + 1] = gi.data[k + 2] = v; gi.data[k + 3] = 255; }
  gc.putImageData(gi, 0, 0);
  c.globalAlpha = .06; c.globalCompositeOperation = 'overlay';
  c.fillStyle = c.createPattern(g, 'repeat'); c.fillRect(0, 0, W * BS, H * BS);
  c.globalAlpha = 1; c.globalCompositeOperation = 'source-over';
}

function drawCompass(c, x, y, r) {
  c.save(); c.translate(x, y);
  c.strokeStyle = 'rgba(230,215,170,.55)'; c.lineWidth = 1;
  c.beginPath(); c.arc(0, 0, r * .72, 0, TAU); c.stroke();
  c.beginPath(); c.arc(0, 0, r * .66, 0, TAU); c.stroke();
  for (let k = 0; k < 8; k++) {
    const a = k * TAU / 8 - Math.PI / 2, len = k % 2 ? r * .55 : r;
    c.fillStyle = k % 2 ? 'rgba(200,180,130,.6)' : 'rgba(240,225,180,.75)';
    c.beginPath(); c.moveTo(0, 0);
    c.lineTo(Math.cos(a - .18) * len * .3, Math.sin(a - .18) * len * .3);
    c.lineTo(Math.cos(a) * len, Math.sin(a) * len);
    c.lineTo(Math.cos(a + .18) * len * .3, Math.sin(a + .18) * len * .3); c.closePath(); c.fill();
  }
  c.font = '700 13px Cinzel, serif'; c.textAlign = 'center'; c.fillStyle = 'rgba(245,230,190,.8)';
  c.fillText('N', 0, -r - 5);
  c.restore();
}

// ---------------------------------------------------------------------------
// Regions
// ---------------------------------------------------------------------------
const PRE = ['Ald', 'Bryn', 'Cor', 'Dun', 'Eld', 'Fen', 'Gar', 'Hal', 'Ivr', 'Kel', 'Lor', 'Mor', 'Nor', 'Ost', 'Rav', 'Sel', 'Thal', 'Ul',
  'Vor', 'Wyn', 'Ash', 'Black', 'Gold', 'Storm', 'Iron', 'Red', 'Grey', 'Frost', 'Hart', 'Raven', 'Elm', 'Wolf', 'Stone', 'Mist', 'Oak', 'Bram'];
const SUF = ['mere', 'hold', 'fell', 'vale', 'reach', 'march', 'watch', 'haven', 'gate', 'ford', 'wood', 'moor', 'crag', 'barrow', 'fen',
  'stead', 'holm', 'keep', 'wick', 'spire', 'hollow', 'bridge', 'cliff', 'dale'];
function genNames(n) {
  const used = new Set(['Crownhold']), out = [];
  while (out.length < n) { const s = PRE[ri(0, PRE.length - 1)] + SUF[ri(0, SUF.length - 1)]; if (!used.has(s)) { used.add(s); out.push(s); } }
  return out;
}

function genRegions() {
  const seeds = [];
  let best = null, bd = 1e9;
  for (let k = 0; k < 6000; k++) {
    const x = rr(W * .3, W * .7), y = rr(H * .3, H * .7), h = hAt(x, y);
    if (h > .06 && h < .32) { const d = Math.hypot(x - W / 2, (y - H / 2) * 1.3); if (d < bd) { bd = d; best = { x, y }; } }
  }
  if (!best) return false;
  seeds.push(best);
  for (let tries = 0; tries < 30000 && seeds.length < 30; tries++) {
    const x = rr(30, W - 30), y = rr(30, H - 30), h = hAt(x, y);
    if (h < .05 || h > .42) continue;
    if (seeds.every(s => Math.hypot(s.x - x, s.y - y) > 128)) seeds.push({ x, y });
  }
  // assign land cells to nearest (warped) seed
  regionOf.fill(-1);
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx; if (height[i] <= 0) continue;
    const x = gx * RES, y = gy * RES;
    const wx = x + (fbm(x * .011, y * .011, 3) - .5) * 110, wy = y + (fbm(x * .011 + 50, y * .011 + 50, 3) - .5) * 110;
    let bi = 0, bdd = 1e18;
    for (let s = 0; s < seeds.length; s++) { const dx = seeds[s].x - wx, dy = seeds[s].y - wy, dd = dx * dx + dy * dy; if (dd < bdd) { bdd = dd; bi = s; } }
    regionOf[i] = bi;
  }
  // merge / drop tiny regions
  for (let pass = 0; pass < 4; pass++) {
    const n = seeds.length, count = new Int32Array(n), shared = new Map();
    for (let i = 0; i < GW * GH; i++) if (regionOf[i] >= 0) count[regionOf[i]]++;
    for (let gy = 0; gy < GH - 1; gy++) for (let gx = 0; gx < GW - 1; gx++) {
      const i = gy * GW + gx, a = regionOf[i]; if (a < 0) continue;
      for (const j of [i + 1, i + GW]) { const b = regionOf[j]; if (b >= 0 && b !== a) { const k = a * 64 + b; shared.set(k, (shared.get(k) || 0) + 1); } }
    }
    const remap = new Int16Array(n).map((_, k) => k);
    let changed = false;
    for (let a = 0; a < n; a++) {
      if (count[a] >= 2200 || a === 0) continue;
      let bb = -1, bc = 0;
      for (let b = 0; b < n; b++) { const c = (shared.get(a * 64 + b) || 0) + (shared.get(b * 64 + a) || 0); if (c > bc && remap[b] === b) { bc = c; bb = b; } }
      if (bb >= 0) { remap[a] = bb; changed = true; } else if (count[a] < 700) { remap[a] = -1; changed = true; }
    }
    if (!changed) break;
    for (let i = 0; i < GW * GH; i++) if (regionOf[i] >= 0) regionOf[i] = remap[regionOf[i]];
  }
  // compact ids
  // seed 0 (the throne) is never merged away, so sorting keeps it at id 0
  const idMap = new Map(); let next = 0;
  for (let i = 0; i < GW * GH; i++) if (regionOf[i] >= 0) idMap.set(regionOf[i], 0);
  [...idMap.keys()].sort((a, b) => a - b).forEach(k => idMap.set(k, next++));
  for (let i = 0; i < GW * GH; i++) if (regionOf[i] >= 0) regionOf[i] = idMap.get(regionOf[i]);
  const n = next;
  if (n < 18) return false;

  // static region borders + distance from region edges
  regionBorder.fill(0); distGrid.fill(255);
  let qt = 0;
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx, r = regionOf[i]; if (r < 0) continue;
    let edge = false, rb = false;
    if (gx === 0 || gy === 0 || gx === GW - 1 || gy === GH - 1) edge = true;
    else for (const j of [i - 1, i + 1, i - GW, i + GW]) { const q = regionOf[j]; if (q !== r) { edge = true; if (q >= 0) rb = true; } }
    if (rb) regionBorder[i] = 1;
    if (edge) { distGrid[i] = 0; bfsQ[qt++] = i; }
  }
  for (let qh = 0; qh < qt; qh++) {
    const i = bfsQ[qh], d = distGrid[i]; if (d >= 40) continue;
    const gx = i % GW;
    for (const j of [gx > 0 ? i - 1 : -1, gx < GW - 1 ? i + 1 : -1, i - GW, i + GW]) {
      if (j < 0 || j >= GW * GH || regionOf[j] !== regionOf[i] || distGrid[j] !== 255) continue;
      distGrid[j] = d + 1; bfsQ[qt++] = j;
    }
  }

  const names = genNames(n);
  regions = [];
  for (let r = 0; r < n; r++) regions.push({ id: r, cells: 0, sx: 0, sy: 0, maxD: 0, adj: new Set(), sea: new Set(), border: [] });
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx, r = regionOf[i]; if (r < 0) continue;
    const R = regions[r]; R.cells++; R.sx += gx; R.sy += gy; R.maxD = Math.max(R.maxD, distGrid[i]);
    if (distGrid[i] === 0) R.border.push(gx, gy);
  }
  const shared = new Map();
  for (let gy = 0; gy < GH - 1; gy++) for (let gx = 0; gx < GW - 1; gx++) {
    const i = gy * GW + gx, a = regionOf[i]; if (a < 0) continue;
    for (const j of [i + 1, i + GW]) { const b = regionOf[j]; if (b >= 0 && b !== a) { const k = Math.min(a, b) * 64 + Math.max(a, b); shared.set(k, (shared.get(k) || 0) + 1); } }
  }
  for (const [k, c] of shared) if (c >= 5) { const a = k >> 6, b = k & 63; regions[a].adj.add(b); regions[b].adj.add(a); }
  // castle site: deep inside region, near centroid
  for (const R of regions) {
    const cx = R.sx / R.cells, cy = R.sy / R.cells, need = Math.min(R.maxD, 9);
    let bi = -1, bs = 1e18;
    for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
      const i = gy * GW + gx; if (regionOf[i] !== R.id || distGrid[i] < need || height[i] > .4) continue;
      const s = (gx - cx) ** 2 + (gy - cy) ** 2; if (s < bs) { bs = s; bi = i; }
    }
    if (bi < 0) for (let i = 0; i < GW * GH; i++) if (regionOf[i] === R.id && distGrid[i] >= need) { bi = i; break; }
    R.x = (bi % GW) * RES; R.y = ((bi / GW) | 0) * RES;
    R.name = R.id === 0 ? 'Crownhold' : names[R.id];
    R.income = R.id === 0 ? 6 : clamp(Math.round(R.cells / 3200) + ri(0, 1), 1, 4);
  }
  // connect islands with sea routes
  seaLinks = [];
  for (;;) {
    const comp = new Int16Array(n).fill(-1); let nc = 0;
    for (let s = 0; s < n; s++) if (comp[s] < 0) {
      const st = [s]; comp[s] = nc;
      while (st.length) { const a = st.pop(); for (const b of [...regions[a].adj, ...regions[a].sea]) if (comp[b] < 0) { comp[b] = nc; st.push(b); } }
      nc++;
    }
    if (nc === 1) break;
    let ba = -1, bb = -1, bdist = 1e18;
    for (let a = 0; a < n; a++) if (comp[a] === 0) for (let b = 0; b < n; b++) if (comp[b] !== 0) {
      const d = Math.hypot(regions[a].x - regions[b].x, regions[a].y - regions[b].y); if (d < bdist) { bdist = d; ba = a; bb = b; }
    }
    regions[ba].sea.add(bb); regions[bb].sea.add(ba); seaLinks.push([ba, bb]);
  }
  // a couple of extra coastal sea lanes for strategic variety
  for (let k = 0; k < 3; k++) {
    let ba = -1, bb = -1, bdist = 1e18;
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) {
      if (regions[a].adj.has(b) || regions[a].sea.has(b)) continue;
      const A = regions[a], B = regions[b], d = Math.hypot(A.x - B.x, A.y - B.y);
      if (d < 200 || d > 420) continue;
      // midpoint must be sea
      let wet = 0; for (let t = .3; t <= .7; t += .1) if (hAt(lerp(A.x, B.x, t), lerp(A.y, B.y, t)) < -.02) wet++;
      if (wet < 5) continue;
      const score = d + rand() * 150; if (score < bdist) { bdist = score; ba = a; bb = b; }
    }
    if (ba >= 0) { regions[ba].sea.add(bb); regions[bb].sea.add(ba); seaLinks.push([ba, bb]); }
  }
  throneId = 0;
  return true;
}

function genAmbience() {
  glints = [];
  for (let k = 0; glints.length < 600 && k < 20000; k++) {
    const x = rr(0, W), y = rr(0, H); if (hAt(x, y) < -.03) glints.push({ x, y, p: rr(0, TAU), s: rr(.6, 1.6), sp: rr(.6, 1.6) });
  }
  clouds = [];
  for (let k = 0; k < 9; k++) clouds.push({ x: rr(0, W), y: rr(0, H), r: rr(110, 240), v: rr(5, 12) });
  seaLabels = [];
  const names = ['The Sundering Sea', 'Gulf of Whispers', 'The Pale Deep', 'Mariner\'s Grave', 'Sea of Embers'];
  const cands = [];
  for (let k = 0; k < 3000; k++) {
    const x = rr(120, W - 120), y = rr(60, H - 60);
    let ok = true;
    for (let dx = -110; dx <= 110 && ok; dx += 22) for (let dy = -24; dy <= 24; dy += 12) if (hAt(x + dx, y + dy) > -.02) { ok = false; break; }
    if (ok) cands.push({ x, y });
  }
  for (const c of cands) {
    if (seaLabels.length >= 3) break;
    if (seaLabels.every(s => Math.hypot(s.x - c.x, s.y - c.y) > 420)) seaLabels.push({ ...c, text: names[seaLabels.length + ri(0, 2)], size: 20, rot: rr(-.12, .12) });
  }
}

// ---------------------------------------------------------------------------
// Ownership overlay
// ---------------------------------------------------------------------------
let overlayDirty = true;
function renderOverlay() {
  const N = GW * GH, d = ovImg.data;
  for (let i = 0; i < N; i++) { const r = regionOf[i]; ownGrid[i] = r < 0 ? -2 : regions[r].owner; }
  const dist = new Uint8Array(N).fill(255);
  let qt = 0;
  for (let gy = 0; gy < GH; gy++) for (let gx = 0; gx < GW; gx++) {
    const i = gy * GW + gx, o = ownGrid[i]; if (o < 0) continue;
    if (gx === 0 || gy === 0 || gx === GW - 1 || gy === GH - 1 ||
      ownGrid[i - 1] !== o || ownGrid[i + 1] !== o || ownGrid[i - GW] !== o || ownGrid[i + GW] !== o) { dist[i] = 0; bfsQ[qt++] = i; }
  }
  const MAXD = 12;
  for (let qh = 0; qh < qt; qh++) {
    const i = bfsQ[qh], dd = dist[i]; if (dd >= MAXD) continue;
    for (const j of [i - 1, i + 1, i - GW, i + GW]) {
      if (j < 0 || j >= N || ownGrid[j] !== ownGrid[i] || dist[j] !== 255) continue;
      dist[j] = dd + 1; bfsQ[qt++] = j;
    }
  }
  for (let i = 0; i < N; i++) {
    const o = i * 4, ow = ownGrid[i];
    if (ow === -2) { d[o + 3] = 0; continue; }
    if (ow >= 0) {
      const c = HOUSES[ow].rgb, dd = dist[i];
      if (dd <= 1) { d[o] = c[0] * .55; d[o + 1] = c[1] * .55; d[o + 2] = c[2] * .55; d[o + 3] = 235; }
      else if (regionBorder[i]) { d[o] = c[0] * .35; d[o + 1] = c[1] * .35; d[o + 2] = c[2] * .35; d[o + 3] = 120; }
      else {
        const f = Math.pow(Math.max(0, 1 - dd / MAXD), 1.6);
        d[o] = c[0]; d[o + 1] = c[1]; d[o + 2] = c[2]; d[o + 3] = (.1 + .5 * f) * 255;
      }
    } else if (regionBorder[i]) { d[o] = 40; d[o + 1] = 28; d[o + 2] = 16; d[o + 3] = 125; }
    else d[o + 3] = 0;
  }
  ovCtx.putImageData(ovImg, 0, 0);
  overlayDirty = false;
}

// ---------------------------------------------------------------------------
// Sigils
// ---------------------------------------------------------------------------
function shieldPath(c, w, h) {
  c.beginPath(); c.moveTo(-w / 2, -h / 2); c.lineTo(w / 2, -h / 2); c.lineTo(w / 2, -h * .05);
  c.quadraticCurveTo(w / 2, h * .36, 0, h / 2); c.quadraticCurveTo(-w / 2, h * .36, -w / 2, -h * .05); c.closePath();
}
function drawEmblem(c, kind, r, col, field) {
  c.fillStyle = col;
  if (kind === 'sun') {
    c.beginPath(); c.arc(0, 0, r * .5, 0, TAU); c.fill();
    for (let k = 0; k < 12; k++) {
      const a = k * TAU / 12, l = k % 2 ? r * .92 : r * 1.1;
      c.beginPath(); c.moveTo(Math.cos(a - .14) * r * .6, Math.sin(a - .14) * r * .6);
      c.lineTo(Math.cos(a) * l, Math.sin(a) * l); c.lineTo(Math.cos(a + .14) * r * .6, Math.sin(a + .14) * r * .6); c.fill();
    }
    c.fillStyle = field; c.beginPath(); c.arc(0, 0, r * .28, 0, TAU); c.globalAlpha = .35; c.fill(); c.globalAlpha = 1;
  } else if (kind === 'moon') {
    c.save(); c.beginPath(); c.arc(0, 0, r * .9, 0, TAU); c.clip();
    c.beginPath(); c.rect(-r * 2, -r * 2, r * 4, r * 4); c.arc(r * .38, -r * .2, r * .74, 0, TAU); c.fill('evenodd');
    c.restore();
    c.beginPath(); c.arc(r * .55, r * .5, r * .12, 0, TAU); c.fill();
    c.beginPath(); c.arc(r * .85, -r * .65, r * .08, 0, TAU); c.fill();
  } else if (kind === 'tower') {
    const w = r * .8, h = r * 1.6;
    c.fillRect(-w / 2, -h / 2 + r * .2, w, h - r * .2);
    for (let k = 0; k < 3; k++) c.fillRect(-w / 2 - r * .1 + k * (w + r * .2) / 2.5, -h / 2, w / 4, r * .32);
    c.fillRect(-w / 2 - r * .12, -h / 2 + r * .28, w + r * .24, r * .12);
    c.fillStyle = field;
    c.beginPath(); c.moveTo(-r * .17, h / 2); c.lineTo(-r * .17, h / 2 - r * .35); c.arc(0, h / 2 - r * .35, r * .17, Math.PI, 0); c.lineTo(r * .17, h / 2); c.fill();
    c.fillRect(-r * .07, -r * .3, r * .14, r * .3);
  } else if (kind === 'flame') {
    const flame = (s) => {
      c.beginPath(); c.moveTo(0, r * s);
      c.bezierCurveTo(-r * .9 * s, r * .6 * s, -r * .7 * s, -r * .2 * s, -r * .1 * s, -r * 1.1 * s);
      c.bezierCurveTo(-r * .05 * s, -r * .5 * s, r * .3 * s, -r * .45 * s, r * .35 * s, -r * .85 * s);
      c.bezierCurveTo(r * .9 * s, -r * .2 * s, r * .8 * s, r * .6 * s, 0, r * s); c.fill();
    };
    flame(1); c.fillStyle = '#ffd36a'; c.save(); c.translate(0, r * .25); flame(.5); c.restore();
  } else if (kind === 'star') {
    c.beginPath();
    for (let k = 0; k < 16; k++) { const a = k * TAU / 16 - Math.PI / 2, l = k % 2 ? r * .38 : (k % 4 ? r * .75 : r * 1.1); c.lineTo(Math.cos(a) * l, Math.sin(a) * l); }
    c.closePath(); c.fill();
  }
}
function drawSigil(c, hi, x, y, w) {
  const Hh = HOUSES[hi], h = w * 1.2;
  c.save(); c.translate(x, y);
  shieldPath(c, w, h);
  const g = c.createLinearGradient(0, -h / 2, 0, h / 2); g.addColorStop(0, Hh.field); g.addColorStop(1, Hh.field2);
  c.fillStyle = g; c.fill();
  c.save(); c.clip();
  const gl = c.createRadialGradient(-w * .2, -h * .3, 0, -w * .2, -h * .3, w); gl.addColorStop(0, 'rgba(255,255,255,.22)'); gl.addColorStop(1, 'rgba(255,255,255,0)');
  c.fillStyle = gl; c.fillRect(-w, -h, w * 2, h * 2);
  c.translate(0, -h * .04);
  drawEmblem(c, Hh.emblem, w * .3, Hh.charge, Hh.field2);
  c.restore();
  shieldPath(c, w, h);
  c.lineWidth = Math.max(1, w * .07); c.strokeStyle = '#c9a25a'; c.stroke();
  c.lineWidth = Math.max(.5, w * .025); c.strokeStyle = 'rgba(0,0,0,.7)'; c.stroke();
  c.restore();
}
function sigilCanvas(cvEl, hi) {
  const c = cvEl.getContext('2d'); c.clearRect(0, 0, cvEl.width, cvEl.height);
  drawSigil(c, hi, cvEl.width / 2, cvEl.height / 2, cvEl.width * .92);
}

// ---------------------------------------------------------------------------
// Game state
// ---------------------------------------------------------------------------
let G = null; // { player, round, gold[], alive[], throne:{owner,count}, over }
let selected = -1, inspected = -1, hover = -1, busy = false;
const armies = [], parts = [];
let shake = 0;

function setupGame(playerHouse) {
  G = { player: playerHouse, round: 1, gold: HOUSES.map(() => 30), alive: HOUSES.map(() => true), throne: { owner: -1, count: 0 }, over: false, current: playerHouse };
  for (const R of regions) { R.owner = -1; R.troops = ri(3, 6); R.walls = rand() < .3 ? 1 : 0; R.moved = false; R.capital = -1; }
  const T = regions[throneId]; T.troops = 14; T.walls = 2;
  // spread capitals by farthest-point sampling
  const caps = [];
  const dist = (a, b) => Math.hypot(regions[a].x - regions[b].x, regions[a].y - regions[b].y);
  for (let h = 0; h < HOUSES.length; h++) {
    let best = -1, bs = -1;
    for (const R of regions) {
      if (R.id === throneId || caps.includes(R.id) || R.adj.has(throneId)) continue;
      const s = Math.min(dist(R.id, throneId) * .8, ...caps.map(c => dist(R.id, c))) + R.adj.size * 8;
      if (s > bs) { bs = s; best = R.id; }
    }
    caps.push(best);
  }
  // shuffle which house gets which seat
  for (let i = caps.length - 1; i > 0; i--) { const j = ri(0, i); [caps[i], caps[j]] = [caps[j], caps[i]]; }
  caps.forEach((c, h) => {
    const R = regions[c]; R.owner = h; R.troops = 10; R.walls = 1; R.capital = h;
    const nb = [...R.adj].find(n => regions[n].owner < 0 && n !== throneId);
    if (nb !== undefined) { regions[nb].owner = h; regions[nb].troops = 5; }
  });
  overlayDirty = true;
  selected = inspected = -1;
}

const owned = h => regions.filter(R => R.owner === h);
const neighbors = R => [...R.adj, ...R.sea];
const isSea = (a, b) => regions[a].sea.has(b) && !regions[a].adj.has(b);
function defStrength(R) {
  const hm = R.owner >= 0 ? HOUSES[R.owner].def : 1;
  return R.troops * (1 + .25 * R.walls + (R.id === throneId ? .2 : 0)) * hm;
}
function attStrength(h, n, from, to) {
  return n * HOUSES[h].atk * (isSea(from, to) && !HOUSES[h].sea ? .8 : 1);
}
function incomeOf(h) {
  let s = 0; for (const R of regions) if (R.owner === h) s += R.income;
  return Math.round(s * HOUSES[h].gold * (season() === 3 ? .5 : 1)) + 3;
}
const season = () => Math.floor((G.round - 1) / 3) % 4;

// ---------------------------------------------------------------------------
// Actions
// ---------------------------------------------------------------------------
function march(fromId, toId, n) {
  const A = regions[fromId], h = A.owner;
  A.troops -= n; A.moved = true;
  return new Promise(res => {
    armies.push({ from: fromId, to: toId, n, h, t: 0, dur: (h === G.player ? .75 : .45) * (FAST ? .02 : 1), done: () => { resolveMarch(h, fromId, toId, n); res(); } });
  });
}
function resolveMarch(h, fromId, toId, n) {
  const B = regions[toId];
  if (B.owner === h) { B.troops += n; B.moved = true; return; }
  const att = attStrength(h, n, fromId, toId) * rr(.85, 1.15);
  const def = defStrength(B) * rr(.85, 1.15);
  const prevOwner = B.owner;
  burst(B.x, B.y, 1);
  if (att > def) {
    const surv = Math.max(1, Math.round(n * Math.sqrt(1 - (def / att) ** 2)));
    floatText(B.x, B.y - 30, `-${n - surv}`, '#ffb070');
    if (B.troops > 0) floatText(B.x + 22, B.y - 14, `-${B.troops}`, '#ff6050');
    B.owner = h; B.troops = surv; B.moved = true; B.walls = Math.max(0, B.walls - 1);
    ring(B.x, B.y, HOUSES[h].map);
    overlayDirty = true;
    if (B.id === throneId) log(`${hn(h)} has seized the <b>Ember Throne</b>!`);
    else if (h === G.player || prevOwner === G.player) log(`${hn(h)} took <b>${B.name}</b>${prevOwner >= 0 ? ' from ' + hn(prevOwner) : ''}.`);
    if (prevOwner >= 0 && owned(prevOwner).length === 0) {
      G.alive[prevOwner] = false;
      log(`${hn(prevOwner)} has been <b>extinguished</b>.`);
      if (prevOwner !== G.player) showBanner(`House ${HOUSES[prevOwner].name} falls`, `Broken by ${HOUSES[h].name}`, 2200);
    }
    if (h === G.player) sfxShake(6);
  } else {
    const surv = Math.max(1, Math.round(B.troops * Math.sqrt(1 - (att / def) ** 2)));
    floatText(B.x, B.y - 30, `-${B.troops - surv}`, '#ffb070');
    floatText(B.x - 22, B.y - 14, `-${n}`, '#ff6050');
    B.troops = surv;
    if (h === G.player) log(`Our assault on <b>${B.name}</b> was repelled.`);
    else if (prevOwner === G.player) log(`${hn(h)} broke upon the walls of <b>${B.name}</b>.`);
    sfxShake(3);
  }
  checkEnd();
  updateHUD();
}
function hn(h) { return `<b style="color:${HOUSES[h].map}">${HOUSES[h].name}</b>`; }

function startHouseTurn(h) {
  G.current = h;
  const inc = incomeOf(h);
  G.gold[h] += inc;
  for (const R of regions) if (R.owner === h) {
    R.moved = false;
    if (season() === 3 && R.troops > 8) R.troops -= Math.ceil(R.troops * .08);
  }
  return inc;
}

// ---------------------------------------------------------------------------
// AI
// ---------------------------------------------------------------------------
function frontierDist(h) {
  const d = new Map(), q = [];
  for (const R of owned(h)) if (neighbors(R).some(n => regions[n].owner !== h)) { d.set(R.id, 0); q.push(R.id); }
  while (q.length) { const a = q.shift(); for (const b of neighbors(regions[a])) if (regions[b].owner === h && !d.has(b)) { d.set(b, d.get(a) + 1); q.push(b); } }
  return d;
}
async function aiTurn(h) {
  // levy & fortify
  const mine = owned(h);
  const threat = R => neighbors(R).reduce((s, n) => s + (regions[n].owner !== h && regions[n].owner >= 0 ? regions[n].troops : 0), 0) - R.troops;
  const frontier = mine.filter(R => neighbors(R).some(n => regions[n].owner !== h));
  if (frontier.length) {
    const key = frontier.find(R => R.id === throneId || R.capital === h);
    if (key && key.walls < 2 && G.gold[h] >= 35 && threat(key) > 0) { G.gold[h] -= 25; key.walls++; }
    while (G.gold[h] >= 10) {
      frontier.sort((a, b) => (threat(b) + (b.id === throneId ? 20 : 0) + rand() * 6) - (threat(a) + (a.id === throneId ? 20 : 0) + rand() * 6));
      frontier[0].troops += 5; G.gold[h] -= 10;
      if (rand() < .25) frontier.push(frontier.shift());
    }
  }
  for (let step = 0; step < 24 && !G.over; step++) {
    let best = null, bv = 0;
    for (const A of owned(h)) {
      if (A.moved || A.troops < 3) continue;
      for (const b of neighbors(A)) {
        const B = regions[b]; if (B.owner === h) continue;
        const ratio = attStrength(h, A.troops - 1, A.id, b) / Math.max(.5, defStrength(B));
        if (ratio < 1.3) continue;
        const v = Math.min(ratio, 3) + (b === throneId ? 1.2 : 0) + B.income * .15 + (B.owner < 0 ? .2 : 0) + (B.owner === G.player ? .25 : 0);
        if (v > bv) { bv = v; best = { a: A.id, b, n: A.troops - 1 }; }
      }
    }
    if (!best) {
      const fd = frontierDist(h);
      for (const A of owned(h)) {
        if (A.moved || A.troops < 3 || (fd.get(A.id) ?? 0) === 0) continue;
        const tgt = neighbors(A).filter(n => regions[n].owner === h).sort((x, y) => (fd.get(x) ?? 99) - (fd.get(y) ?? 99))[0];
        if (tgt !== undefined) { best = { a: A.id, b: tgt, n: A.troops - 1 }; break; }
      }
    }
    if (!best) break;
    await march(best.a, best.b, best.n);
  }
}

// ---------------------------------------------------------------------------
// Turn flow
// ---------------------------------------------------------------------------
async function endTurn() {
  if (busy || G.over) return;
  busy = true; selected = -1; updateHUD();
  for (let h = 0; h < HOUSES.length && !G.over; h++) {
    if (h === G.player || !G.alive[h]) continue;
    startHouseTurn(h);
    updateHUD();
    await aiTurn(h);
    await sleep(FAST ? 0 : 120);
  }
  if (G.over) return;
  // end of round: throne
  const tOwner = regions[throneId].owner;
  if (tOwner >= 0) {
    G.throne.count = G.throne.owner === tOwner ? G.throne.count + 1 : 1; G.throne.owner = tOwner;
    if (G.throne.count >= 3) { finish(tOwner === G.player, tOwner === G.player
      ? `For three turns your banner flew above Crownhold. House ${HOUSES[G.player].name} sits the Ember Throne.`
      : `House ${HOUSES[tOwner].name} held the Ember Throne for three turns. Your house kneels — or burns.`); return; }
    if (G.throne.count === 2) log(`${hn(tOwner)} will claim the crown if they hold the throne one more turn!`);
  } else G.throne = { owner: -1, count: 0 };
  const prevSeason = season();
  G.round++;
  if (season() !== prevSeason) showBanner(SEASONS[season()].name, SEASONS[season()].sub, 2400);
  const inc = startHouseTurn(G.player);
  log(`Turn ${G.round}: the treasury gains <b>${inc}</b> gold.`);
  busy = false;
  updateHUD();
}

function checkEnd() {
  if (G.over) return;
  if (!G.alive[G.player]) { finish(false, `The last keep of House ${HOUSES[G.player].name} has fallen. Your name will be forgotten.`); return; }
  if (G.alive.every((a, h) => !a || h === G.player)) finish(true, `Every rival house lies broken. The realm of Aldmere bows to House ${HOUSES[G.player].name}.`);
}
function finish(win, text) {
  G.over = true; busy = true;
  setTimeout(() => {
    $('endTitle').textContent = win ? 'Victory' : 'Defeat';
    $('endText').textContent = text;
    $('endScreen').classList.remove('hidden');
  }, 1200);
}

// ---------------------------------------------------------------------------
// Player input
// ---------------------------------------------------------------------------
function onTap(sx, sy) {
  if (!G || G.over) return;
  const w = toWorld(sx, sy);
  const r = pickRegion(w.x, w.y);
  if (busy) { inspected = r; updateHUD(); return; }
  if (r < 0) { selected = -1; inspected = -1; updateHUD(); return; }
  const R = regions[r];
  if (selected >= 0 && r !== selected && neighbors(regions[selected]).includes(r)) {
    const A = regions[selected];
    const n = A.troops - 1;
    if (n > 0) {
      busy = true; const from = selected; selected = -1;
      march(from, r, n).then(() => { busy = G.over; inspected = r; if (regions[r].owner === G.player && !regions[r].moved) selected = r; updateHUD(); });
    }
    updateHUD(); return;
  }
  if (selected === r) { selected = -1; inspected = r; }
  else if (R.owner === G.player && !R.moved && R.troops > 1) { selected = r; inspected = r; }
  else { selected = -1; inspected = r; }
  updateHUD();
}
function pickRegion(x, y) {
  const gx = x / RES | 0, gy = y / RES | 0;
  if (gx >= 0 && gy >= 0 && gx < GW && gy < GH) { const r = regionOf[gy * GW + gx]; if (r >= 0) return r; }
  // tap near a castle in the sea / edge
  let best = -1, bd = 30 / Math.min(cam.z, 1);
  for (const R of regions) { const d = Math.hypot(R.x - x, R.y - y); if (d < bd) { bd = d; best = R.id; } }
  return best;
}
$('btnRecruit').onclick = () => {
  const R = regions[inspected]; if (!R || R.owner !== G.player || G.gold[G.player] < 10 || busy) return;
  G.gold[G.player] -= 10; R.troops += 5; floatText(R.x, R.y - 30, '+5', '#ffe08a'); ring(R.x, R.y, '#ffe08a'); updateHUD();
};
$('btnFortify').onclick = () => {
  const R = regions[inspected]; if (!R || R.owner !== G.player || G.gold[G.player] < 25 || R.walls >= 3 || busy) return;
  G.gold[G.player] -= 25; R.walls++; floatText(R.x, R.y - 30, 'Walls raised', '#e0e0ff'); ring(R.x, R.y, '#dfe6ff'); updateHUD();
};
$('btnEnd').onclick = endTurn;
$('btnAgain').onclick = () => { $('endScreen').classList.add('hidden'); newWorld(); showTitle(); };
addEventListener('keydown', e => {
  if (!G || $('hud').classList.contains('hidden')) return;
  if (e.key === 'Enter' || e.key === 'e') endTurn();
  if (e.key === 'r') $('btnRecruit').click();
  if (e.key === 'f') $('btnFortify').click();
  if (e.key === 'Escape') { selected = -1; updateHUD(); }
});

// ---------------------------------------------------------------------------
// HUD
// ---------------------------------------------------------------------------
const rivalCanvases = [];
function buildRivals() {
  const el = $('rivals'); el.innerHTML = ''; rivalCanvases.length = 0;
  HOUSES.forEach((Hh, h) => {
    const row = document.createElement('div'); row.className = 'rv';
    const c = document.createElement('canvas'); c.width = 40; c.height = 48; sigilCanvas(c, h);
    row.appendChild(c);
    const n = document.createElement('span'); n.className = 'n'; n.textContent = Hh.name + (h === G.player ? ' (you)' : ''); row.appendChild(n);
    const s = document.createElement('span'); s.className = 's'; row.appendChild(s);
    el.appendChild(row); rivalCanvases.push(row);
  });
}
function updateHUD() {
  if (!G) return;
  const p = G.player, mine = owned(p);
  $('hudGold').textContent = G.gold[p];
  $('hudRealms').textContent = mine.length;
  $('hudTroops').textContent = mine.reduce((s, R) => s + R.troops, 0);
  $('hudTurn').textContent = G.round;
  $('hudSeason').textContent = SEASONS[season()].name;
  const tO = regions[throneId].owner;
  $('hudThrone').innerHTML = tO < 0 ? 'Unclaimed' : `<span style="color:${HOUSES[tO].map}">${HOUSES[tO].name}</span> ${tO === G.throne.owner ? G.throne.count : 0}/3`;
  HOUSES.forEach((_, h) => {
    const row = rivalCanvases[h]; if (!row) return;
    const o = owned(h);
    row.classList.toggle('dead', !G.alive[h]);
    row.querySelector('.s').textContent = G.alive[h] ? `${o.length} · ${o.reduce((s, R) => s + R.troops, 0)}⚔` : '—';
  });
  const R = regions[inspected];
  const info = $('regionInfo');
  if (!R) {
    info.innerHTML = busy && G.current !== p ? `<div class="hint">House ${HOUSES[G.current].name} is moving its hosts…</div>`
      : `<div class="hint">Tap one of your holdings to command it, then tap a neighbouring land to march.</div>`;
  } else {
    const ownerTxt = R.owner < 0 ? 'Unsworn lords' : `House ${HOUSES[R.owner].name}${R.owner === p ? ' (yours)' : ''}`;
    const tags = [R.id === throneId ? '♛ Seat of the Ember Throne' : '', R.capital >= 0 ? `Ancestral seat of ${HOUSES[R.capital].name}` : ''].filter(Boolean).join('<br>');
    info.innerHTML = `<div class="rname">${R.name}</div><div class="rowner" style="color:${R.owner >= 0 ? HOUSES[R.owner].map : '#c8b088'}">${ownerTxt}</div>
      ${tags ? `<div class="rowner">${tags}</div>` : ''}
      <div class="rrow"><span>Garrison</span><span>${R.troops}</span></div>
      <div class="rrow"><span>Walls</span><span>${'▮'.repeat(R.walls) || 'none'}</span></div>
      <div class="rrow"><span>Income</span><span>${R.income}g</span></div>
      ${R.owner === p ? `<div class="rrow"><span>Orders</span><span>${R.moved ? 'spent' : selected === R.id ? 'select target' : 'ready'}</span></div>` : ''}`;
  }
  const mineSel = R && R.owner === p && !busy;
  $('btnRecruit').disabled = !(mineSel && G.gold[p] >= 10);
  $('btnFortify').disabled = !(mineSel && G.gold[p] >= 25 && R.walls < 3);
  $('btnEnd').disabled = busy;
}
const logEl = $('log');
function log(html) {
  const d = document.createElement('div'); d.innerHTML = html; logEl.appendChild(d);
  while (logEl.children.length > 12) logEl.removeChild(logEl.firstChild);
}
let bannerTimer = 0;
function showBanner(text, sub, ms) {
  const b = $('banner'); b.innerHTML = `${text}${sub ? `<small>${sub}</small>` : ''}`; b.classList.add('show');
  clearTimeout(bannerTimer); bannerTimer = setTimeout(() => b.classList.remove('show'), ms);
}

// ---------------------------------------------------------------------------
// Camera & pointer
// ---------------------------------------------------------------------------
let sw = 0, sh = 0, dpr = 1;
const cam = { x: W / 2, y: H / 2, z: 1 };
const fitZ = () => Math.min(sw / W, sh / H);
function resize() {
  sw = innerWidth; sh = innerHeight; dpr = Math.min(2, devicePixelRatio || 1);
  cv.width = sw * dpr; cv.height = sh * dpr; vignette = null; clampCam();
}
function clampCam() {
  cam.z = clamp(cam.z, fitZ() * .9, Math.max(3, fitZ() * 5));
  const m = 60, hw = sw / 2 / cam.z, hh = sh / 2 / cam.z;
  cam.x = W + 2 * m > hw * 2 ? clamp(cam.x, hw - m, W + m - hw) : W / 2;
  cam.y = H + 2 * m > hh * 2 ? clamp(cam.y, hh - m, H + m - hh) : H / 2;
}
const toWorld = (sx, sy) => ({ x: (sx - sw / 2) / cam.z + cam.x, y: (sy - sh / 2) / cam.z + cam.y });
addEventListener('resize', resize);

const pointers = new Map(); let drag = null, pinch = null;
cv.addEventListener('pointerdown', e => {
  cv.setPointerCapture(e.pointerId);
  pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pointers.size === 1) drag = { sx: e.clientX, sy: e.clientY, cx: cam.x, cy: cam.y, moved: false };
  else if (pointers.size === 2) {
    const [a, b] = [...pointers.values()];
    pinch = { d: Math.hypot(a.x - b.x, a.y - b.y), z: cam.z, w: toWorld((a.x + b.x) / 2, (a.y + b.y) / 2) };
    drag = null;
  }
});
cv.addEventListener('pointermove', e => {
  if (pointers.has(e.pointerId)) pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pinch && pointers.size >= 2) {
    const [a, b] = [...pointers.values()];
    cam.z = pinch.z * Math.hypot(a.x - b.x, a.y - b.y) / pinch.d; clampCam();
    const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    cam.x = pinch.w.x - (mx - sw / 2) / cam.z; cam.y = pinch.w.y - (my - sh / 2) / cam.z; clampCam();
  } else if (drag && pointers.size === 1) {
    const dx = e.clientX - drag.sx, dy = e.clientY - drag.sy;
    if (Math.hypot(dx, dy) > 7) drag.moved = true;
    if (drag.moved) { cam.x = drag.cx - dx / cam.z; cam.y = drag.cy - dy / cam.z; clampCam(); }
  } else if (e.pointerType === 'mouse' && G) {
    const w = toWorld(e.clientX, e.clientY); hover = pickRegion(w.x, w.y);
    cv.style.cursor = hover >= 0 && (regions[hover].owner === G.player || (selected >= 0 && neighbors(regions[selected]).includes(hover))) ? 'pointer' : 'default';
  }
});
const endPointer = e => {
  if (!pointers.has(e.pointerId)) return;
  pointers.delete(e.pointerId);
  if (drag && !drag.moved && pointers.size === 0 && e.type === 'pointerup') onTap(e.clientX, e.clientY);
  if (pointers.size < 2) pinch = null;
  if (pointers.size === 1) { const [p] = [...pointers.values()]; drag = { sx: p.x, sy: p.y, cx: cam.x, cy: cam.y, moved: true }; }
  if (pointers.size === 0) drag = null;
};
cv.addEventListener('pointerup', endPointer);
cv.addEventListener('pointercancel', endPointer);
cv.addEventListener('wheel', e => {
  e.preventDefault();
  const w = toWorld(e.clientX, e.clientY);
  cam.z *= Math.exp(-e.deltaY * .0015); clampCam();
  cam.x = w.x - (e.clientX - sw / 2) / cam.z; cam.y = w.y - (e.clientY - sh / 2) / cam.z; clampCam();
}, { passive: false });

// ---------------------------------------------------------------------------
// Particles & FX
// ---------------------------------------------------------------------------
function burst(x, y, k) {
  for (let i = 0; i < 46 * k; i++) {
    const a = rr(0, TAU), s = rr(20, 120);
    parts.push({ t: 'ember', x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s - 40, life: 0, max: rr(.5, 1.3), s: rr(1, 2.6), c: rand() < .5 ? '#ffb347' : '#ff6a2a' });
  }
  for (let i = 0; i < 14 * k; i++) parts.push({ t: 'smoke', x: x + rr(-10, 10), y: y + rr(-8, 4), vx: rr(-12, 12), vy: rr(-30, -10), life: 0, max: rr(1.2, 2.2), s: rr(8, 14) });
  parts.push({ t: 'flash', x, y, life: 0, max: .35, s: 60 });
}
function ring(x, y, c) { parts.push({ t: 'ring', x, y, life: 0, max: .9, s: 70, c }); }
function floatText(x, y, txt, c) { parts.push({ t: 'text', x, y, vx: 0, vy: -24, life: 0, max: 1.6, txt, c }); }
function sfxShake(a) { shake = Math.max(shake, a); }

const snow = [];
for (let i = 0; i < 260; i++) snow.push({ x: Math.random(), y: Math.random(), s: Math.random() * 2 + .6, v: Math.random() * 30 + 20, p: Math.random() * TAU });
const motes = [];
for (let i = 0; i < 60; i++) motes.push({ x: Math.random(), y: Math.random(), s: Math.random() * 1.6 + .5, p: Math.random() * TAU });

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------
let vignette = null, time = 0, iconS = 1;
function drawCastle(c, R, t) {
  const x = R.x, y = R.y, s = iconS * (R.id === throneId ? 1.35 : R.capital >= 0 ? 1.12 : 1);
  const own = R.owner >= 0 ? HOUSES[R.owner] : null;
  const roof = own ? own.map : '#7d6f5c';
  c.save(); c.translate(x, y); c.scale(s, s);
  if (R.id === throneId) {
    const g = c.createRadialGradient(0, -14, 2, 0, -14, 46);
    g.addColorStop(0, `rgba(255,190,90,${.45 + .15 * Math.sin(t * 2)})`); g.addColorStop(1, 'rgba(255,140,40,0)');
    c.fillStyle = g; c.fillRect(-50, -60, 100, 100);
  }
  c.fillStyle = 'rgba(0,0,0,.4)'; c.beginPath(); c.ellipse(2, 2, 17, 6, 0, 0, TAU); c.fill();
  const stone = c.createLinearGradient(-12, 0, 12, 0);
  const s1 = R.id === throneId ? '#f0dcae' : '#e2d6bd', s2 = R.id === throneId ? '#9b7d4c' : '#8a7f6c';
  stone.addColorStop(0, s1); stone.addColorStop(1, s2);
  c.strokeStyle = 'rgba(25,18,10,.9)'; c.lineWidth = .9;
  // curtain wall
  if (R.walls > 0) {
    c.fillStyle = stone; c.fillRect(-15, -5, 30, 7); c.strokeRect(-15, -5, 30, 7);
    for (let k = 0; k < 6; k++) { c.fillRect(-15 + k * 5.4, -7.5, 3, 2.5); }
    if (R.walls > 1) { c.fillRect(-18, -9, 6, 11); c.strokeRect(-18, -9, 6, 11); c.fillRect(12, -9, 6, 11); c.strokeRect(12, -9, 6, 11); }
  }
  // towers
  c.fillStyle = stone;
  c.fillRect(-11, -14, 6, 14); c.strokeRect(-11, -14, 6, 14);
  c.fillRect(5, -14, 6, 14); c.strokeRect(5, -14, 6, 14);
  c.fillRect(-5, -20, 10, 20); c.strokeRect(-5, -20, 10, 20);
  // roofs
  c.fillStyle = roof;
  for (const [cx, by, w, h] of [[-8, -14, 4.5, 7], [8, -14, 4.5, 7], [0, -20, 6.5, 9]]) {
    c.beginPath(); c.moveTo(cx - w, by); c.lineTo(cx, by - h); c.lineTo(cx + w, by); c.closePath(); c.fill(); c.stroke();
  }
  c.fillStyle = 'rgba(20,12,6,.9)';
  c.beginPath(); c.moveTo(-2, 0); c.lineTo(-2, -4); c.arc(0, -4, 2, Math.PI, 0); c.lineTo(2, 0); c.fill();
  c.fillStyle = `rgba(255,200,110,${.65 + .3 * Math.sin(t * 3 + R.id)})`;
  c.fillRect(-1, -14, 2, 3); c.fillRect(-9, -10, 2, 2.4); c.fillRect(7, -10, 2, 2.4);
  // banner
  c.strokeStyle = '#2a1d10'; c.lineWidth = .8;
  c.beginPath(); c.moveTo(0, -29); c.lineTo(0, -40); c.stroke();
  c.fillStyle = own ? own.field : '#d8ccb0';
  c.beginPath(); c.moveTo(0, -40);
  for (let k = 0; k <= 6; k++) c.lineTo(k * 2, -40 + Math.sin(t * 5 + k * .9 + R.id) * 1.1);
  for (let k = 6; k >= 0; k--) c.lineTo(k * 2, -34.5 + Math.sin(t * 5 + k * .9 + R.id) * 1.1);
  c.closePath(); c.fill();
  if (own) { c.fillStyle = own.charge; c.beginPath(); c.arc(6, -37.3 + Math.sin(t * 5 + 2.7 + R.id) * 1.1, 1.4, 0, TAU); c.fill(); }
  // crown
  if (R.id === throneId) {
    c.save(); c.translate(0, -50 + Math.sin(t * 1.6) * 1.5);
    const cg = c.createLinearGradient(0, -7, 0, 5); cg.addColorStop(0, '#fff3b8'); cg.addColorStop(1, '#c47f1c');
    c.fillStyle = cg; c.strokeStyle = '#4a2c06'; c.lineWidth = .8;
    c.beginPath(); c.moveTo(-9, 4); c.lineTo(-10, -5); c.lineTo(-5, -1); c.lineTo(0, -8); c.lineTo(5, -1); c.lineTo(10, -5); c.lineTo(9, 4); c.closePath();
    c.fill(); c.stroke();
    c.fillStyle = '#d4202a'; c.beginPath(); c.arc(0, 1, 1.6, 0, TAU); c.fill();
    c.restore();
  }
  c.restore();
}

function drawBadge(c, R) {
  const s = iconS, x = R.x, y = R.y + 12 * s;
  const own = R.owner >= 0 ? HOUSES[R.owner] : null;
  const txt = String(R.troops);
  c.font = `700 ${11 * s}px Cinzel, Georgia, serif`;
  const w = Math.max(18 * s, c.measureText(txt).width + 10 * s), h = 14 * s;
  c.beginPath(); c.roundRect(x - w / 2, y - h / 2, w, h, 4 * s);
  c.fillStyle = own ? own.field : 'rgba(60,50,38,.92)'; c.fill();
  c.lineWidth = 1.2 * s; c.strokeStyle = own ? own.charge : '#b9a37a'; c.stroke();
  c.fillStyle = '#fff6e0'; c.textAlign = 'center'; c.textBaseline = 'middle';
  c.fillText(txt, x, y + .5 * s);
  if (R.owner === G.player && R.moved) { c.fillStyle = 'rgba(0,0,0,.45)'; c.beginPath(); c.roundRect(x - w / 2, y - h / 2, w, h, 4 * s); c.fill(); }
}
function drawLabel(c, R) {
  const s = iconS, sz = (R.id === throneId ? 13 : 11) * s;
  c.font = `700 ${sz}px Cinzel, Georgia, serif`;
  c.textAlign = 'center'; c.textBaseline = 'alphabetic';
  const y = R.y - (R.id === throneId ? 76 : 48) * s;
  c.lineWidth = 3 * s; c.strokeStyle = 'rgba(15,10,5,.75)'; c.lineJoin = 'round';
  c.strokeText(R.name, R.x, y);
  c.fillStyle = R.id === throneId ? '#ffe2a0' : '#f3e6c8';
  c.fillText(R.name, R.x, y);
}

function drawRegionOutline(c, R, col, alpha, w) {
  c.fillStyle = col; c.globalAlpha = alpha;
  const b = R.border, sz = RES * w;
  for (let k = 0; k < b.length; k += 2) c.fillRect(b[k] * RES - sz / 2 + 1, b[k + 1] * RES - sz / 2 + 1, sz, sz);
  c.globalAlpha = 1;
}
function arc(A, B, lift) {
  const mx = (A.x + B.x) / 2, my = (A.y + B.y) / 2, d = Math.hypot(B.x - A.x, B.y - A.y);
  return { x0: A.x, y0: A.y, cx: mx, cy: my - d * lift, x1: B.x, y1: B.y };
}
const qpt = (q, t) => ({ x: (1 - t) ** 2 * q.x0 + 2 * (1 - t) * t * q.cx + t * t * q.x1, y: (1 - t) ** 2 * q.y0 + 2 * (1 - t) * t * q.cy + t * t * q.y1 });
function drawArrow(c, A, B, col, alpha, t) {
  const q = arc(A, B, .25);
  const t0 = .22, t1 = .8;
  c.globalAlpha = alpha; c.strokeStyle = col; c.lineWidth = 3.2 * iconS; c.lineCap = 'round';
  c.setLineDash([7 * iconS, 6 * iconS]); c.lineDashOffset = -t * 30;
  c.beginPath(); let p = qpt(q, t0); c.moveTo(p.x, p.y);
  for (let k = 1; k <= 16; k++) { p = qpt(q, t0 + (t1 - t0) * k / 16); c.lineTo(p.x, p.y); }
  c.stroke(); c.setLineDash([]);
  const p2 = qpt(q, t1), p1 = qpt(q, t1 - .03), a = Math.atan2(p2.y - p1.y, p2.x - p1.x), s = 9 * iconS;
  c.fillStyle = col; c.beginPath(); c.moveTo(p2.x + Math.cos(a) * s, p2.y + Math.sin(a) * s);
  c.lineTo(p2.x + Math.cos(a + 2.4) * s, p2.y + Math.sin(a + 2.4) * s); c.lineTo(p2.x + Math.cos(a - 2.4) * s, p2.y + Math.sin(a - 2.4) * s); c.fill();
  c.globalAlpha = 1;
}
function drawArmy(c, a) {
  const A = regions[a.from], B = regions[a.to], q = arc(A, B, .3);
  const e = a.t < .5 ? 2 * a.t * a.t : 1 - (-2 * a.t + 2) ** 2 / 2;
  const p = qpt(q, e), Hh = HOUSES[a.h], s = iconS * 1.1;
  // trail
  for (let k = 1; k <= 8; k++) { const pp = qpt(q, Math.max(0, e - k * .025)); c.fillStyle = rgba(Hh.rgb, .35 * (1 - k / 9)); c.beginPath(); c.arc(pp.x, pp.y, 3 * s * (1 - k / 10), 0, TAU); c.fill(); }
  c.fillStyle = 'rgba(0,0,0,.35)'; c.beginPath(); c.ellipse(p.x + 2, p.y + 4 * s, 9 * s, 3 * s, 0, 0, TAU); c.fill();
  c.save(); c.translate(p.x, p.y); c.scale(s, s);
  c.strokeStyle = '#2b1c0e'; c.lineWidth = 1.2; c.beginPath(); c.moveTo(0, 4); c.lineTo(0, -22); c.stroke();
  c.fillStyle = Hh.field; c.beginPath(); c.moveTo(0, -22);
  for (let k = 0; k <= 7; k++) c.lineTo(k * 2.2, -22 + Math.sin(time * 9 + k) * 1.4);
  for (let k = 7; k >= 0; k--) c.lineTo(k * 2.2, -12 + Math.sin(time * 9 + k) * 1.4);
  c.closePath(); c.fill(); c.strokeStyle = Hh.charge; c.lineWidth = .7; c.stroke();
  c.font = '700 9px Cinzel, serif'; c.textAlign = 'center'; c.textBaseline = 'middle';
  c.fillStyle = '#fff'; c.lineWidth = 2.5; c.strokeStyle = 'rgba(0,0,0,.8)';
  c.strokeText(a.n, 0, 11); c.fillText(a.n, 0, 11);
  c.restore();
}

function render(dt) {
  time += dt;
  // world transform
  const shx = shake ? rr(-shake, shake) : 0, shy = shake ? rr(-shake, shake) : 0;
  shake = Math.max(0, shake - dt * 25);
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#0a1a26'; ctx.fillRect(0, 0, cv.width, cv.height);
  ctx.setTransform(dpr * cam.z, 0, 0, dpr * cam.z, dpr * (sw / 2 - cam.x * cam.z + shx), dpr * (sh / 2 - cam.y * cam.z + shy));
  iconS = clamp(.9 / cam.z, .9, 2.2);
  ctx.imageSmoothingEnabled = true; ctx.imageSmoothingQuality = 'high';

  // outer ocean beyond map edges
  ctx.fillStyle = '#0b2235'; ctx.fillRect(-W, -H, W * 3, H * 3);
  ctx.drawImage(baseCv, 0, 0, W, H);

  // sea glints
  ctx.fillStyle = '#e8f6ff';
  for (const g of glints) {
    const a = Math.pow(Math.max(0, Math.sin(time * g.sp + g.p)), 10);
    if (a < .05) continue;
    ctx.globalAlpha = a * .7; ctx.beginPath(); ctx.ellipse(g.x, g.y, 3.5 * g.s, .8 * g.s, 0, 0, TAU); ctx.fill();
  }
  ctx.globalAlpha = 1;

  if (G) {
    if (overlayDirty) renderOverlay();
    ctx.drawImage(ovCv, 0, 0, W, H);
  }

  // season tint
  if (G) {
    const se = season();
    if (se === 3) { ctx.fillStyle = 'rgba(215,232,255,.2)'; ctx.fillRect(0, 0, W, H); }
    else if (se === 2) { ctx.fillStyle = 'rgba(200,110,40,.07)'; ctx.fillRect(0, 0, W, H); }
    else if (se === 1) { ctx.fillStyle = 'rgba(255,230,150,.05)'; ctx.fillRect(0, 0, W, H); }
  }

  // sea lanes
  ctx.strokeStyle = 'rgba(235,225,190,.55)'; ctx.lineWidth = 1.6 * iconS; ctx.setLineDash([2 * iconS, 6 * iconS]); ctx.lineDashOffset = -time * 8;
  for (const [a, b] of seaLinks) {
    const q = arc(regions[a], regions[b], .12);
    ctx.beginPath(); ctx.moveTo(q.x0, q.y0); ctx.quadraticCurveTo(q.cx, q.cy, q.x1, q.y1); ctx.stroke();
  }
  ctx.setLineDash([]);

  if (G) {
    if (hover >= 0 && hover !== selected) drawRegionOutline(ctx, regions[hover], '#fff4d0', .35, 1);
    if (selected >= 0) {
      const S = regions[selected];
      drawRegionOutline(ctx, S, '#ffd56a', .7 + .3 * Math.sin(time * 5), 1.6);
      for (const n of neighbors(S)) {
        const B = regions[n], enemy = B.owner !== G.player;
        drawArrow(ctx, S, B, enemy ? '#ff5a3c' : '#ffe9a8', n === hover ? 1 : .75, time);
      }
    } else if (inspected >= 0) drawRegionOutline(ctx, regions[inspected], '#fff4d0', .55, 1.2);
  }

  // cloud shadows
  for (const cl of clouds) {
    cl.x += cl.v * dt; if (cl.x - cl.r > W + 100) { cl.x = -cl.r - 100; cl.y = rr(0, H); }
    const g = ctx.createRadialGradient(cl.x, cl.y, 0, cl.x, cl.y, cl.r);
    g.addColorStop(0, 'rgba(0,10,20,.16)'); g.addColorStop(1, 'rgba(0,10,20,0)');
    ctx.fillStyle = g; ctx.fillRect(cl.x - cl.r, cl.y - cl.r, cl.r * 2, cl.r * 2);
  }

  // castles, sorted by y
  if (G) {
    const sorted = [...regions].sort((a, b) => a.y - b.y);
    for (const R of sorted) drawCastle(ctx, R, time);
    for (const R of sorted) if (cam.z * iconS > .55 || R.id === throneId || R.capital >= 0) drawLabel(ctx, R);
    for (const R of sorted) drawBadge(ctx, R);
    if (selected >= 0) {
      const S = regions[selected];
      ctx.strokeStyle = `rgba(255,220,120,${.6 + .4 * Math.sin(time * 6)})`; ctx.lineWidth = 2 * iconS;
      ctx.beginPath(); ctx.ellipse(S.x, S.y + 2, 24 * iconS, 9 * iconS, 0, 0, TAU); ctx.stroke();
    }
  }

  // armies
  for (let i = armies.length - 1; i >= 0; i--) {
    const a = armies[i]; a.t += dt / a.dur;
    if (a.t >= 1) { armies.splice(i, 1); a.done(); continue; }
    drawArmy(ctx, a);
  }

  // particles
  for (let i = parts.length - 1; i >= 0; i--) {
    const p = parts[i]; p.life += dt;
    const k = p.life / p.max; if (k >= 1) { parts.splice(i, 1); continue; }
    if (p.vx !== undefined) { p.x += p.vx * dt; p.y += p.vy * dt; }
    if (p.t === 'ember') {
      p.vx *= .97; p.vy = p.vy * .97 - 20 * dt;
      ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = 1 - k; ctx.fillStyle = p.c;
      ctx.beginPath(); ctx.arc(p.x, p.y, p.s * iconS, 0, TAU); ctx.fill();
      ctx.globalCompositeOperation = 'source-over';
    } else if (p.t === 'smoke') {
      ctx.globalAlpha = .45 * (1 - k); ctx.fillStyle = '#3a3330';
      ctx.beginPath(); ctx.arc(p.x, p.y, p.s * (1 + k * 1.8) * iconS, 0, TAU); ctx.fill();
    } else if (p.t === 'flash') {
      const g = ctx.createRadialGradient(p.x, p.y, 0, p.x, p.y, p.s * iconS);
      g.addColorStop(0, `rgba(255,230,160,${1 - k})`); g.addColorStop(1, 'rgba(255,120,30,0)');
      ctx.globalCompositeOperation = 'lighter'; ctx.fillStyle = g; ctx.fillRect(p.x - p.s * iconS, p.y - p.s * iconS, p.s * 2 * iconS, p.s * 2 * iconS);
      ctx.globalCompositeOperation = 'source-over';
    } else if (p.t === 'ring') {
      ctx.globalAlpha = 1 - k; ctx.strokeStyle = p.c; ctx.lineWidth = 3 * iconS * (1 - k) + .5;
      ctx.beginPath(); ctx.ellipse(p.x, p.y, p.s * k * iconS, p.s * k * .45 * iconS, 0, 0, TAU); ctx.stroke();
    } else if (p.t === 'text') {
      ctx.globalAlpha = Math.min(1, (1 - k) * 2); ctx.font = `700 ${14 * iconS}px Cinzel, serif`; ctx.textAlign = 'center';
      ctx.lineWidth = 3 * iconS; ctx.strokeStyle = 'rgba(0,0,0,.8)'; ctx.strokeText(p.txt, p.x, p.y); ctx.fillStyle = p.c; ctx.fillText(p.txt, p.x, p.y);
    }
    ctx.globalAlpha = 1;
  }

  // ---- screen space ----
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  if (G && season() === 3) {
    ctx.fillStyle = '#fff';
    for (const f of snow) {
      f.y += f.v * dt / sh; f.x += Math.sin(time + f.p) * .0004; if (f.y > 1) { f.y = 0; f.x = Math.random(); }
      ctx.globalAlpha = .75; ctx.beginPath(); ctx.arc(f.x * sw, f.y * sh, f.s, 0, TAU); ctx.fill();
    }
    ctx.globalAlpha = 1;
  } else {
    ctx.fillStyle = '#ffe2a0';
    for (const m of motes) {
      m.y -= dt * .006; if (m.y < 0) m.y = 1;
      ctx.globalAlpha = .25 + .2 * Math.sin(time * 1.3 + m.p);
      ctx.beginPath(); ctx.arc((m.x + Math.sin(time * .2 + m.p) * .02) * sw, m.y * sh, m.s, 0, TAU); ctx.fill();
    }
    ctx.globalAlpha = 1;
  }
  if (!vignette) {
    vignette = ctx.createRadialGradient(sw / 2, sh / 2, Math.min(sw, sh) * .35, sw / 2, sh / 2, Math.hypot(sw, sh) * .62);
    vignette.addColorStop(0, 'rgba(0,0,0,0)'); vignette.addColorStop(1, 'rgba(5,3,1,.72)');
  }
  ctx.fillStyle = vignette; ctx.fillRect(0, 0, sw, sh);
}

let last = performance.now();
function frame(now) {
  const dt = Math.min(.05, (now - last) / 1000); last = now;
  if (titleMode) { cam.x = W / 2 + Math.sin(time * .05) * W * .12; cam.y = H / 2 + Math.cos(time * .04) * H * .08; clampCam(); }
  render(dt);
  requestAnimationFrame(frame);
}

// ---------------------------------------------------------------------------
// Boot
// ---------------------------------------------------------------------------
let titleMode = true;
const FAST = location.hash.includes('fast');
function newWorld() {
  for (let attempt = 0; attempt < 12; attempt++) {
    const seed = (Math.random() * 1e9) | 0;
    rand = mulberry32(seed); seedNoise(); genHeight();
    if (genRegions()) break;
  }
  genAmbience();
  bakeBase();
  G = null; armies.length = 0; parts.length = 0;
}
function showTitle() {
  titleMode = true;
  $('hud').classList.add('hidden'); $('title').classList.remove('hidden');
  cam.z = Math.max(fitZ() * 1.25, .5);
  const hc = $('houseChoice'); hc.innerHTML = '';
  HOUSES.forEach((Hh, h) => {
    const card = document.createElement('div'); card.className = 'hcard';
    const c = document.createElement('canvas'); c.width = 144; c.height = 172; sigilCanvas(c, h);
    card.appendChild(c);
    card.insertAdjacentHTML('beforeend', `<div class="hn">House ${Hh.name}</div><div class="hw">“${Hh.words}”</div><div class="hp">${Hh.trait}</div>`);
    card.onclick = () => startGame(h);
    hc.appendChild(card);
  });
}
function startGame(h) {
  rand = Math.random;
  setupGame(h);
  titleMode = false;
  $('title').classList.add('hidden'); $('hud').classList.remove('hidden');
  sigilCanvas($('hudSigil'), h);
  $('hudHouse').textContent = 'House ' + HOUSES[h].name;
  $('hudWords').textContent = '“' + HOUSES[h].words + '”';
  logEl.innerHTML = '';
  buildRivals();
  busy = false;
  const cap = regions.find(R => R.capital === h);
  cam.z = Math.max(fitZ(), Math.min(1.1, sh / H * 1.4)); cam.x = cap.x; cam.y = cap.y; clampCam();
  startHouseTurn(h); G.gold[h] = 30;
  log(`The banners of ${hn(h)} rise over <b>${cap.name}</b>.`);
  log(`Hold <b>Crownhold</b> for three turns to claim the Ember Throne.`);
  showBanner(`House ${HOUSES[h].name}`, `“${HOUSES[h].words}”`, 2400);
  inspected = cap.id; selected = cap.troops > 1 ? cap.id : -1;
  updateHUD();
}

resize();
newWorld();
showTitle();
requestAnimationFrame(frame);
if (document.fonts) document.fonts.ready.then(() => { bakeBase(); });
// debug hooks for automated checks: #play=<house>&turns=<n>&sel
const hp = new URLSearchParams(location.hash.slice(1));
if (hp.has('play')) {
  startGame(+hp.get('play'));
  (async () => { for (let k = 0; k < +(hp.get('turns') || 0) && !G.over; k++) { await endTurn(); } updateHUD();
    console.log('RESULT round=' + G.round + ' over=' + G.over + ' alive=' + G.alive + ' throne=' + JSON.stringify(G.throne) + ' counts=' + HOUSES.map((_, h) => owned(h).length)); })();
}
window.__CE = { get G() { return G; }, get regions() { return regions; }, startGame, endTurn };
})();
