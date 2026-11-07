// Two browsers playing through a relay that only forwards messages. Nobody deals: the cards are
// shuffled by both players with locks only their owner can open, and every card played carries the
// key that proves it was in the player's hand. Moves are encoded by the engine (Message in game.bend).
import { Data, Effect, Schedule } from "effect";
import G, { type Held, type List, type Opp } from "../engine/game.ts";
import { CARD_VALUES, P, inv, modPow, randKey, randomHex, sha256, shuffle } from "./crypto.ts";

export class Cheat extends Data.TaggedError("Cheat")<{ reason: string }> {}
export class Disconnected extends Data.TaggedError("Disconnected")<{ reason: string }> {}

const local = typeof location !== "undefined" && ["localhost", "127.0.0.1"].includes(location.hostname);
const param = typeof location !== "undefined" ? new URLSearchParams(location.search).get("relay") : null;
// After deploying relay/, put its address here (or pass ?relay=wss://... in the page URL).
export const RELAY_URL = param ?? (local ? "ws://127.0.0.1:8799" : "wss://recreio-relay.williansugiyama.workers.dev");

const RESIGN = 4294967295;
const HEX = /^[0-9a-f]{1,520}$/;
const LOOKUP = new Map(CARD_VALUES.map((v, i) => [v.toString(16), i]));
const hexes = (xs: bigint[]) => xs.map((x) => x.toString(16));

type Msg = { t: string; [k: string]: unknown };

// message kinds as the engine numbers them (Proto.order in game.bend)
const KIND: Record<string, number> = { commit: 1, reveal: 2, d1: 3, d2: 4, d3: 5, d4: 6, keys: 7, move: 8, resign: 9 };
const NAME = Object.fromEntries(Object.entries(KIND).map(([k, v]) => [v, k]));

function readDeck(deck: unknown): bigint[] {
  if (!Array.isArray(deck) || deck.length !== 18) throw new Cheat({ reason: "baralho inválido" });
  return deck.map((h) => {
    if (typeof h !== "string" || !HEX.test(h)) throw new Cheat({ reason: "baralho inválido" });
    const v = BigInt("0x" + h);
    if (v <= 1n || v >= P) throw new Cheat({ reason: "baralho inválido" });
    return v;
  });
}

export type Coins = { blue: number; red: number };
export type Dealt = { mine: [number, number]; table: number };

export class Session {
  onMove: (code: number) => void = () => {};
  onResign: () => void = () => {};
  onCheat: (reason: string) => void = () => {};
  onLeft: () => void = () => {};
  private queue: Msg[] = [];
  private waiters: (() => void)[] = [];
  private peer = false;
  private closed = false;
  private ws!: WebSocket;
  private keys: bigint[] = [];
  private F: bigint[] = [];
  // what to accept and what to reveal is decided by the engine (laws "jogo online" in LAWS.bend)
  private mine: List<Held> = { $: "Nil" };
  private opp: Opp | null = null;
  private step = 0; // setup step, as the engine counts it (5 once the deal is done)

  readonly code: string;
  readonly host: boolean;
  private constructor(code: string, host: boolean) {
    this.code = code;
    this.host = host;
  }

  /** Joins the room `code` on the relay (retried twice). */
  static open(url: string, code: string, host: boolean): Effect.Effect<Session, Disconnected> {
    const s = new Session(code, host);
    const connect = Effect.async<Session, Disconnected>((resume) => {
      const ws = new WebSocket(`${url}/room/${code}`);
      s.ws = ws;
      ws.onopen = () => resume(Effect.succeed(s));
      ws.onerror = () => resume(Effect.fail(new Disconnected({ reason: "Não consegui entrar na sala (código errado, sala cheia ou sem conexão)." })));
      ws.onclose = () => { if (!s.closed) s.onLeft(); };
      ws.onmessage = (e) => { try { s.receive(JSON.parse(String(e.data))); } catch { s.onCheat("mensagem inválida"); } };
    });
    return connect.pipe(Effect.retry(Schedule.addDelay(Schedule.recurs(2), () => "400 millis")));
  }

  close() { this.closed = true; this.ws?.close(); }
  private send(m: Msg) { this.ws.send(JSON.stringify(m)); }
  private wake() { const w = this.waiters; this.waiters = []; for (const f of w) f(); }

  private receive(m: Msg) {
    if (m.t === "peer") { this.peer = true; return this.wake(); }
    if (m.t === "left") return this.onLeft();
    // the engine decides: take it, hold it for its turn, or call it cheating
    if (G.api_proto_order(this.host ? 1 : 0, this.step, KIND[m.t] ?? 0).$ === "Cheat") return this.onCheat("mensagem fora de ordem");
    if (m.t === "move") return this.gotMove(m);
    if (m.t === "resign") return G.api_msg_read(String(m.m)) === RESIGN ? this.onResign() : this.onCheat("mensagem inválida");
    this.queue.push(m);
    this.wake();
  }

  /** The next message of type `t`. */
  private next(t: string): Effect.Effect<Msg> {
    return Effect.async<Msg>((resume) => {
      const look = () => {
        const i = this.queue.findIndex((m) => m.t === t);
        if (i >= 0) resume(Effect.succeed(this.queue.splice(i, 1)[0]));
        else this.waiters.push(look);
      };
      look();
    });
  }

  /** The next setup message, in the order the engine expects them. */
  private take(): Effect.Effect<Msg> {
    return this.next(NAME[G.api_proto_expected(this.host ? 1 : 0, this.step)]).pipe(
      Effect.tap(() => Effect.sync(() => {
        this.step++;
        // once the deal is done, any setup message still waiting was repeated
        if (this.step === 5 && this.queue.length) this.onCheat("mensagem fora de ordem");
      })),
    );
  }

  waitPeer(): Effect.Effect<void> {
    return Effect.async<void>((resume) => {
      const look = () => (this.peer ? resume(Effect.void) : this.waiters.push(look));
      look();
    });
  }

  /** Who starts: each side flips a secret coin (0 or 1) and sends a hash of it first, so nobody can
   *  change it after seeing the other's. The engine turns both coins into the starter. */
  coin(bit: number): Effect.Effect<Coins, Cheat> {
    const self = this;
    return Effect.gen(function* () {
      const nonce = randomHex(16);
      self.send({ t: "commit", c: yield* Effect.promise(() => sha256(`${bit}:${nonce}`)) });
      const theirs = yield* self.take();
      self.send({ t: "reveal", n: bit, nonce });
      const rev = yield* self.take();
      const check = yield* Effect.promise(() => sha256(`${rev.n}:${rev.nonce}`));
      const theirBit = Number.isInteger(rev.n) && (rev.n as number) >= 0 && (rev.n as number) < 2 ** 32 ? (rev.n as number) : 2;
      if (!G.api_proto_coin_ok(check === theirs.c ? 1 : 0, theirBit)) return yield* new Cheat({ reason: "no sorteio de quem começa" });
      const other = rev.n as number;
      return { blue: self.host ? bit : other, red: self.host ? other : bit };
    });
  }

  /** The draw. Blue (host) gets positions 0 and 1, red 2 and 3, position 4 is the table card. */
  deal(): Effect.Effect<Dealt, Cheat> {
    const self = this;
    return Effect.gen(function* () {
      const e = randKey(), eInv = inv(e);
      self.keys = Array.from({ length: 18 }, randKey);
      const read = (m: Msg) => Effect.try({ try: () => readDeck(m.deck), catch: (x) => (x instanceof Cheat ? x : new Cheat({ reason: "baralho inválido" })) });
      let F: bigint[];
      if (self.host) {
        self.send({ t: "d1", deck: hexes(shuffle(CARD_VALUES.map((x) => modPow(x, e)))) });
        const d2 = yield* read(yield* self.take());
        self.send({ t: "d3", deck: hexes(d2.map((x, k) => modPow(modPow(x, eInv), self.keys[k]))) });
        F = yield* read(yield* self.take());
      } else {
        const d1 = yield* read(yield* self.take());
        self.send({ t: "d2", deck: hexes(shuffle(d1.map((x) => modPow(x, e)))) });
        const d3 = yield* read(yield* self.take());
        F = d3.map((x, k) => modPow(modPow(x, eInv), self.keys[k]));
        self.send({ t: "d4", deck: hexes(F) });
      }
      self.F = F;
      const h = self.host ? 1 : 0;
      const myPos = [0, 1].map((i) => G.api_proto_mine(h, i)), handed = [0, 1, 2].map((i) => G.api_proto_handed(h, i));
      // hand over the keys the engine says to: the other player's cards and the table card
      self.send({ t: "keys", k: Object.fromEntries(handed.map((k) => [k, inv(self.keys[k]).toString(16)])) });
      const got = ((yield* self.take()).k ?? {}) as Record<string, unknown>;
      const open = (k: number) => {
        const key = got[k];
        if (typeof key !== "string" || !HEX.test(key)) return undefined;
        return LOOKUP.get(modPow(modPow(F[k], BigInt("0x" + key)), inv(self.keys[k])).toString(16));
      };
      const mine = myPos.map(open), table = open(4);
      if (mine.some((c) => c === undefined) || table === undefined) return yield* new Cheat({ reason: "no sorteio" });
      self.mine = G.api_mine_start(h, mine[0] as number, mine[1] as number);
      self.opp = G.api_opp_start(h, table);
      return { mine: mine as [number, number], table };
    });
  }

  sendMove(code: number, card: number) {
    const msg: Msg = { t: "move", m: G.api_msg_move(code) };
    const k = G.api_mine_pos(this.mine, card);
    if (k !== 99) Object.assign(msg, { pos: k, key: inv(this.keys[k]).toString(16) });
    this.mine = G.api_mine_play(this.mine, card);
    if (this.opp) this.opp = G.api_opp_i_played(this.opp, card);
    this.send(msg);
  }

  sendResign() { this.send({ t: "resign", m: G.api_msg_resign() }); }

  private gotMove(m: Msg) {
    const read = G.api_msg_read(String(m.m));
    if (!read || read === RESIGN) return this.onCheat("mensagem inválida");
    if (!this.opp) return this.onCheat("jogada antes do sorteio");
    const code = read - 1, card = G.api_move_card(code);
    // the page does the cryptography: what card does the sent key open at the sent position?
    const pos = m.pos as number;
    const hasProof = Number.isInteger(pos) && pos >= 0 && pos < this.F.length && typeof m.key === "string" && HEX.test(m.key);
    const opened = hasProof ? (LOOKUP.get(modPow(modPow(this.F[pos], BigInt("0x" + m.key)), inv(this.keys[pos])).toString(16)) ?? 99) : 99;
    // the engine decides whether that proves the card
    const v = G.api_opp_play(this.opp, card, hasProof ? 1 : 0, hasProof ? pos : 0, opened);
    if (v.$ === "Rejected") return this.onCheat(v.reason === 1 ? "carta jogada sem prova" : "a carta jogada não era da mão dele");
    this.opp = v.opp;
    this.onMove(code);
  }

}
