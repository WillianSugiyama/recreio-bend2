// The table's painted materials, drawn once on canvases: felt with chalk markings, and wood grain.
import * as THREE from "three";
import { W, HOMES } from "../engine/index.ts";

/** Felt covers the board plus this margin (in squares) on each side; the goals are painted in it. */
export const FELT_MARGIN = 0.55;
export const FELT_SIZE = W + FELT_MARGIN * 2;

function rng(seed: number) {
  return () => ((seed = (seed * 1664525 + 1013904223) >>> 0) / 4294967296);
}

function chalkLine(ctx: CanvasRenderingContext2D, r: () => number, pts: [number, number][], width: number) {
  for (let pass = 0; pass < 3; pass++) {
    ctx.beginPath();
    ctx.lineWidth = width * (0.75 + r() * 0.5);
    ctx.strokeStyle = `rgba(241,239,230,${0.28 + r() * 0.18})`;
    pts.forEach(([x, y], i) => {
      const jx = x + (r() - 0.5) * width * 0.6, jy = y + (r() - 0.5) * width * 0.6;
      if (i === 0) ctx.moveTo(jx, jy); else ctx.lineTo(jx, jy);
    });
    ctx.stroke();
  }
}

export function feltTexture(): THREE.CanvasTexture {
  const S = 2048, px = S / FELT_SIZE;
  const c = document.createElement("canvas");
  c.width = c.height = S;
  const ctx = c.getContext("2d")!;
  const r = rng(7);
  ctx.fillStyle = "#1d6a3b";
  ctx.fillRect(0, 0, S, S);
  // fibers: thousands of short strokes a shade lighter or darker than the felt
  for (let i = 0; i < 90000; i++) {
    const x = r() * S, y = r() * S, a = r() * Math.PI, l = 2 + r() * 5;
    ctx.strokeStyle = r() < 0.5 ? `rgba(12,58,30,${0.18 + r() * 0.2})` : `rgba(64,140,86,${0.1 + r() * 0.16})`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(x, y);
    ctx.lineTo(x + Math.cos(a) * l, y + Math.sin(a) * l);
    ctx.stroke();
  }
  const at = (col: number, row: number): [number, number] => [(FELT_MARGIN + col) * px, (FELT_MARGIN + row) * px];
  const lw = px * 0.035;
  // the grid
  for (let i = 0; i <= W; i++) {
    chalkLine(ctx, r, [at(i, 0), at(i, W)], lw);
    chalkLine(ctx, r, [at(0, i), at(W, i)], lw);
  }
  // center circle and spot on the middle square
  const mid = (W - 1) / 2 + 0.5;
  const circle: [number, number][] = [];
  for (let k = 0; k <= 72; k++) { const a = (k / 72) * Math.PI * 2; circle.push(at(mid + Math.cos(a) * 1.15, mid + Math.sin(a) * 1.15)); }
  ctx.globalAlpha = 0.7;
  chalkLine(ctx, r, circle, lw);
  ctx.globalAlpha = 1;
  // goals: each teacher's home square is a goal mouth,, with the net painted in the margin
  for (const home of HOMES) {
    const col = home % W, row = Math.floor(home / W), top = row === 0;
    const edge = top ? 0 : W, inward = top ? 1 : -1;
    // the goal line: a heavier stroke along the home square's outer edge
    chalkLine(ctx, r, [at(col, edge), at(col + 1, edge)], lw * 2.4);
    // the spot in the middle of the home square
    const [sx, sy] = at(col + 0.5, row + 0.5);
    ctx.fillStyle = "rgba(241,239,230,0.55)";
    ctx.beginPath(); ctx.arc(sx, sy, px * 0.07, 0, Math.PI * 2); ctx.fill();
  }
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  t.anisotropy = 8;
  return t;
}

export function woodTexture(): THREE.CanvasTexture {
  const w = 1024, h = 256;
  const c = document.createElement("canvas");
  c.width = w; c.height = h;
  const ctx = c.getContext("2d")!;
  const r = rng(11);
  ctx.fillStyle = "#8a5530";
  ctx.fillRect(0, 0, w, h);
  for (let i = 0; i < 160; i++) {
    const y = r() * h, amp = 2 + r() * 6, freq = 0.004 + r() * 0.01, phase = r() * 10;
    ctx.strokeStyle = r() < 0.6 ? `rgba(52,26,10,${0.18 + r() * 0.28})` : `rgba(176,112,60,${0.14 + r() * 0.2})`;
    ctx.lineWidth = 0.6 + r() * 2.2;
    ctx.beginPath();
    for (let x = 0; x <= w; x += 8) {
      const yy = y + Math.sin(x * freq + phase) * amp + Math.sin(x * freq * 3.1 + phase) * amp * 0.3;
      if (x === 0) ctx.moveTo(x, yy); else ctx.lineTo(x, yy);
    }
    ctx.stroke();
  }
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  t.wrapS = t.wrapT = THREE.RepeatWrapping;
  return t;
}

/** A chalk smear: soft at the edges, tapered at both ends, grainy inside (used as an alpha map). */
export function scuffTexture(): THREE.CanvasTexture {
  const w = 256, h = 64;
  const c = document.createElement("canvas");
  c.width = w; c.height = h;
  const ctx = c.getContext("2d")!;
  const r = rng(23);
  for (let i = 0; i < 2600; i++) {
    const x = r() * w, y = h / 2 + (r() + r() + r() - 1.5) * h * 0.32;
    const taper = Math.sin((x / w) * Math.PI);
    const a = taper * (0.25 + r() * 0.5) * Math.max(0, 1 - Math.abs(y - h / 2) / (h * 0.42));
    ctx.fillStyle = `rgba(255,255,255,${a})`;
    ctx.fillRect(x, y, 1 + r() * 3, 1 + r() * 1.5);
  }
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

/** Goal netting: a white mesh on transparency. */
export function netTexture(): THREE.CanvasTexture {
  const S = 128, c = document.createElement("canvas");
  c.width = c.height = S;
  const ctx = c.getContext("2d")!;
  ctx.strokeStyle = "rgba(245,243,236,0.95)";
  ctx.lineWidth = 6;
  for (let k = 0; k <= S; k += 64) {
    ctx.beginPath(); ctx.moveTo(k, 0); ctx.lineTo(k, S); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(0, k); ctx.lineTo(S, k); ctx.stroke();
  }
  const t = new THREE.CanvasTexture(c);
  t.wrapS = t.wrapT = THREE.RepeatWrapping;
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

/** Chalk grain: speckled alpha that repeats along a stroke, so arrows look hand-drawn on felt. */
export function chalkGrainTexture(): THREE.CanvasTexture {
  const w = 128, h = 32, c = document.createElement("canvas");
  c.width = w; c.height = h;
  const ctx = c.getContext("2d")!;
  const r = rng(41);
  for (let i = 0; i < 1800; i++) {
    const y = r() * h, edge = Math.abs(y - h / 2) / (h / 2);
    ctx.fillStyle = `rgba(255,255,255,${(0.35 + r() * 0.65) * (1 - edge * edge * 0.85)})`;
    ctx.fillRect(r() * w, y, 1 + r() * 2.5, 1 + r() * 1.5);
  }
  const t = new THREE.CanvasTexture(c);
  t.wrapS = THREE.RepeatWrapping;
  return t;
}
