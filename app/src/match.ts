// The match: screens, turns, the bot, the online session. Rules are always asked of the engine.
import { useSyncExternalStore } from "react";
import { Effect, Exit, Cause } from "effect";
import { G, W, CELLS, UNKNOWN, decode, type Game, type Move, type Side } from "./engine/index.ts";
import { botMove, odds, rand32, type Odds } from "./ai.ts";
import { RELAY_URL, Session } from "./net/online.ts";

export type Screen = "menu" | "game";
/** A button on the table. Pieces keep an identity so the table can animate them. */
export type PieceView = { id: number; owner: Side; teacher: boolean; sq: number; alive: boolean; knock?: { at: number; dx: number; dz: number } };
export type Over = { title: string; reason: string; won: boolean | null };

export type State = {
  screen: Screen;
  mode: "bot" | "online" | null;
  level: number;
  me: Side;
  g: Game | null;
  pieces: PieceView[];
  cardPick: number | null;
  sel: number | null;
  last: (Move & { at: number }) | null;
  focusSq: number | null;
  replaying: boolean;
  /** The turn clock: when the current turn's time runs out (performance.now ms), or null. */
  clockEndsAt: number | null;
  notice: { text: string; at: number } | null;
  busy: boolean;
  over: Over | null;
  odds: Odds | null;
  room: { code: string; host: boolean; status: string; error: boolean } | null;
  opponent: string;
};

const LEVELS = ["Fácil", "Médio", "Difícil"];

// the buttons standing in their starting places, for the table behind the menu
const restingPieces = () => piecesFrom(G.api_new(1, 2));

let state: State = {
  screen: "menu", mode: null, level: 1, me: 0, g: null, pieces: [], cardPick: null, sel: null, last: null, focusSq: null, replaying: false, clockEndsAt: null, notice: null,
  busy: false, over: null, odds: null, room: null,
  opponent: "Bot",
};
const listeners = new Set<() => void>();
const set = (patch: Partial<State>) => { state = { ...state, ...patch }; for (const l of listeners) l(); };
export const useMatch = () => useSyncExternalStore((l) => { listeners.add(l); return () => listeners.delete(l); }, () => state);
export const getMatch = () => state;

queueMicrotask(() => set({ pieces: restingPieces() }));

let session: Session | null = null;
// the buttons as they stood before the last move, so the move can be watched again
let before: PieceView[] = [];

// ---- the turn clock: 30 seconds per move. Watching a move again ("Ver de novo") spends them too.
export const TURN_SECONDS = 30;
const startClock = (g: Game) => set({ clockEndsAt: G.api_outcome(g) ? null : performance.now() + TURN_SECONDS * 1000 });

// the clock stands still while "Como jogar" is open
let pausedLeft: number | null = null;
export function pauseClock() {
  // a new turn can start while paused (the bot answers): keep the newest time left
  if (state.clockEndsAt == null) return;
  pausedLeft = state.clockEndsAt - performance.now();
  set({ clockEndsAt: null });
}
export function resumeClock() {
  if (pausedLeft == null) return;
  if (state.g && !state.over) set({ clockEndsAt: performance.now() + pausedLeft });
  pausedLeft = null;
}

// when your time runs out, the clock plays a legal move for you (any one); the rules stay untouched
setInterval(() => {
  const s = state, g = s.g;
  if (!g || s.over || s.screen !== "game" || s.clockEndsAt == null || performance.now() < s.clockEndsAt) return;
  if (G.api_turn(g) !== s.me || s.busy) return;
  if (!G.api_move_count(g)) return;
  const m = decode(G.api_bot(g, 0, rand32()));
  if (s.mode === "online") { session?.sendMove(m.code, m.card); set({ busy: true }); }
  set({ notice: { text: "O tempo acabou: o relógio jogou por você.", at: performance.now() }, replaying: false });
  applied(G.api_play(g, m.code), m);
}, 250);
// every button the table draws gets a never-reused id, so a new match or a replay remounts it fresh
let nextId = 0;
let oddsToken = 0;

// ---- pieces with identity

// what the table must show, straight from the engine's scene (laws "o que a mesa desenha")
type Token = { owner: Side; teacher: boolean; sq: number };
function tokens(g: Game): Token[] {
  return Array.from({ length: G.api_token_count(g) }, (_, i) => {
    const t = G.api_token(g, i), code = Math.floor(t / 64);
    return { owner: (code <= 2 ? 0 : 1) as Side, teacher: code % 2 === 0, sq: t % 64 };
  });
}

function piecesFrom(g: Game): PieceView[] {
  return tokens(g).map((t) => ({ id: ++nextId, ...t, alive: true }));
}

function movePieces(pieces: PieceView[], m: Move, g: Game): PieceView[] {
  const now = performance.now();
  const ddx = (m.to % W) - (m.from % W), ddz = Math.floor(m.to / W) - Math.floor(m.from / W);
  const len = Math.hypot(ddx, ddz) || 1;
  const dx = ddx / len, dz = ddz / len;
  const next = pieces.map((p) => {
    if (!p.alive) return p;
    if (p.sq === m.to) return { ...p, alive: false, knock: { at: now, dx, dz } };
    if (p.sq === m.from) return { ...p, sq: m.to };
    return p;
  });
  // the engine is the truth: if our picture drifted, rebuild it from the board
  const alive = next.filter((p) => p.alive);
  const want = tokens(g);
  const same = alive.length === want.length && want.every((t) => alive.some((p) => p.sq === t.sq && p.owner === t.owner && p.teacher === t.teacher));
  return same ? next : [...next.filter((p) => !p.alive), ...piecesFrom(g)];
}

// ---- turns

export const myMoves = (s: State = state): Move[] => {
  if (!s.g || s.busy || s.replaying || s.over || G.api_turn(s.g) !== s.me) return [];
  return Array.from({ length: G.api_move_count(s.g) }, (_, i) => decode(G.api_move(s.g as Game, i)));
};

async function refreshOdds() {
  const token = ++oddsToken;
  const g = state.g;
  if (!g) return;
  const o = await odds(g, state.me);
  if (token === oddsToken) set({ odds: o });
}

const ENDINGS = {
  Playing: "",
  KeeperTaken: "O goleiro foi capturado.",
  ReachedGoal: "Uma peça chegou no gol adversário.",
  Repeated: "A mesma posição se repetiu 3 vezes.",
  Stalled: "20 rodadas seguidas sem nenhuma captura.",
};

function finish(out: number, reason?: string) {
  const g = state.g as Game;
  const won = out === 3 ? null : out === 1 + state.me;
  const other = state.mode === "bot" ? "O bot" : "O outro jogador";
  reason ??= ENDINGS[G.api_ending(g).$];
  set({ over: { title: out === 3 ? "Empate" : won ? "Você venceu" : `${other} venceu`, reason, won }, busy: false, clockEndsAt: null });
}

function applied(g: Game, m: Move) {
  before = state.pieces;
  startClock(g);
  set({ g, pieces: movePieces(state.pieces, m, g), last: { ...m, at: performance.now() }, sel: null, cardPick: null });
  refreshOdds();
  const out = G.api_outcome(g);
  if (out) return void setTimeout(() => finish(out), 900);
  if (state.mode === "bot" && G.api_turn(g) !== state.me) botTurn();
}

async function botTurn() {
  set({ busy: true });
  const [code] = await Promise.all([botMove(state.g as Game, state.level), new Promise((r) => setTimeout(r, 650))]);
  if (!state.g || state.over) return;
  set({ busy: false });
  applied(G.api_play(state.g, code), decode(code));
}

/** Plays the last move again on the table: the buttons it touched jump back, then it happens once more. */
export function replayLast() {
  const g = state.g, m = state.last;
  if (!g || !m || state.replaying) return;
  // fresh ids make the table remount those buttons at their old squares instead of sliding them back
  const back = before.map((p) => (p.alive && (p.sq === m.from || p.sq === m.to) ? { ...p, id: ++nextId } : p));
  set({ pieces: back, replaying: true, sel: null, cardPick: null });
  setTimeout(() => {
    if (state.g !== g) return;
    set({ pieces: movePieces(back, m, g), last: { ...m, at: performance.now() } });
    setTimeout(() => set({ replaying: false }), 900);
  }, 550);
}

export function pickCard(id: number) {
  set({ cardPick: state.cardPick === id ? null : id });
}

export function clickSquare(sq: number) {
  const g = state.g;
  if (!g) return;
  // while the table is busy no card counts as picked, so a tap can only select
  const card = state.busy || state.replaying ? UNKNOWN : (state.cardPick ?? UNKNOWN);
  const c = G.api_click(g, state.me, card, state.sel ?? CELLS, sq);
  if (c.$ === "Crowded") return set({ notice: { text: "Mais de um botão chega aí: toque primeiro no botão que vai.", at: performance.now() } });
  if (c.$ === "Select") return set({ sel: c.sq });
  if (c.$ === "Clear") return set({ sel: null });
  const target = decode(G.api_move_code(c.card, c.from, c.to));
  if (state.mode === "online") { session?.sendMove(target.code, target.card); set({ busy: true }); }
  applied(G.api_play_move(g, c.card, c.from, c.to), target);
}

function startGame(g: Game, me: Side, opponent: string) {
  const who = G.api_turn(g) === me ? "você começa" : `${state.mode === "bot" ? "o bot" : "seu amigo"} começa`;
  set({ screen: "game", g, me, opponent, pieces: piecesFrom(g), sel: null, cardPick: null, last: null, busy: false, over: null, odds: null, notice: { text: `Sorteio: ${who}.`, at: performance.now() } });
  refreshOdds();
  startClock(g);
  if (state.mode === "bot" && G.api_turn(g) !== me) botTurn();
  if (state.mode === "online") set({ busy: G.api_turn(g) !== me });
}

// ---- menu, and who starts: a secret coin from each side, so neither decides it alone

export const setLevel = (level: number) => set({ level });
export const setFocusSq = (focusSq: number | null) => set({ focusSq });

export function playBot() {
  session?.close(); session = null;
  set({ mode: "bot", me: 0, room: null, over: null });
  startGame(G.api_new(rand32(), rand32()), 0, `Bot ${LEVELS[state.level].toLowerCase()}`);
}

const roomStatus = (status: string, error = false) => state.room && set({ room: { ...state.room, status, error } });

async function startOnline(s: Session) {
  roomStatus("Sorteando quem começa…");
  const coin = await Effect.runPromiseExit(s.coin(rand32() % 2));
  if (Exit.isFailure(coin)) return roomStatus("Trapaça detectada no sorteio de quem começa.", true);
  roomStatus("Embaralhando as cartas com criptografia…");
  const dealt = await Effect.runPromiseExit(s.deal());
  if (Exit.isFailure(dealt)) return roomStatus("Trapaça detectada no sorteio das cartas.", true);
  const { mine, table } = dealt.value;
  const [b0, b1, r0, r1] = state.me === 0 ? [...mine, UNKNOWN, UNKNOWN] : [UNKNOWN, UNKNOWN, ...mine];
  startGame(G.api_new_dealt(G.api_starter(coin.value.blue, coin.value.red), b0, b1, r0, r1, table), state.me, "Seu amigo");
}

// ---- online

async function goOnline(code: string, host: boolean) {
  session?.close(); session = null;
  set({ mode: "online", me: host ? 0 : 1, room: { code, host, error: false, status: host ? "Mande o código para o seu amigo. Esperando ele entrar…" : "Entrando na sala…" } });
  const exit = await Effect.runPromiseExit(Session.open(RELAY_URL, code, host));
  if (Exit.isFailure(exit)) {
    const err = Cause.failureOption(exit.cause);
    return set({ room: { code, host, error: true, status: err._tag === "Some" ? err.value.reason : "Não consegui entrar na sala." } });
  }
  const s = exit.value;
  session = s;
  s.onMove = (code) => {
    const before = G.api_turn(state.g as Game);
    const g = G.api_play_revealed(state.g as Game, code);
    if (G.api_turn(g) === before) return finish(state.me + 1, "O outro jogador mandou uma jogada inválida.");
    set({ busy: false });
    applied(g, decode(code));
  };
  s.onResign = () => finish(state.me + 1, "O outro jogador desistiu.");
  s.onCheat = (why) => finish(state.me + 1, `Trapaça detectada: ${why}.`);
  s.onLeft = () => { if (!state.over && state.g) finish(state.me + 1, "O outro jogador saiu da partida."); };
  await Effect.runPromise(s.waitPeer());
  await startOnline(s);
}

export const createRoom = () => goOnline(String(100000 + (rand32() % 900000)), true);
export const joinRoom = (code: string) => goOnline(code.trim(), false);

export function resign() {
  if (state.over || !state.g) return;
  if (state.mode === "online") session?.sendResign();
  finish(2 - state.me, "Você desistiu.");
}

export function toMenu() {
  session?.close(); session = null;
  oddsToken++;
  set({ screen: "menu", g: null, pieces: restingPieces(), over: null, room: null, busy: false, odds: null, me: 0, clockEndsAt: null, notice: null });
}

export const again = () => playBot();
