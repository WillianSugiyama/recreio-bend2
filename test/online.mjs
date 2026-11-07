// Two simulated players through the local relay (wrangler dev on :8799): odd-or-even, the
// cryptographic draw, a full game with proofs, and a cheater who plays a card it does not have.
import { Effect } from "../app/node_modules/effect/dist/esm/index.js";
import G from "../engine/game.mjs";
import { Session } from "../app/src/net/online.ts";
const run = (e) => Effect.runPromise(e);

const URL = "ws://127.0.0.1:8799";
const pick = (n) => crypto.getRandomValues(new Uint32Array(1))[0] % n;

async function pair(code) {
  const a = await run(Session.open(URL, code, true));
  const b = await run(Session.open(URL, code, false));
  await Promise.all([run(a.waitPeer()), run(b.waitPeer())]);
  const [pa, pb] = await Promise.all([run(a.coin(1)), run(b.coin(0))]);
  if (JSON.stringify(pa) !== JSON.stringify(pb)) throw new Error("coins disagree");
  const t = performance.now();
  const [da, db] = await Promise.all([run(a.deal()), run(b.deal())]);
  const ms = performance.now() - t;
  if (da.table !== db.table) throw new Error("table card disagrees");
  if (new Set([...da.mine, ...db.mine, da.table]).size !== 5) throw new Error("cards repeat");
  const starter = G.api_starter(pa.blue, pa.red);
  return { a, b, pa, da, db, starter, ms };
}

// ---- an honest full game
{
  const { a, b, pa, da, db, starter, ms } = await pair("111111");
  console.log("coins", JSON.stringify(pa), "starter", starter, "deal", da.mine, db.mine, "table", da.table, `(${ms.toFixed(0)} ms)`);
  const P = [
    { o: a, me: 0, g: G.api_new_dealt(starter, ...da.mine, 99, 99, da.table) },
    { o: b, me: 1, g: G.api_new_dealt(starter, 99, 99, ...db.mine, db.table) },
  ];
  let cheats = 0;
  for (const p of P) p.o.onCheat = (w) => { cheats++; console.log("unexpected cheat:", w); };
  let plies = 0;
  while (G.api_outcome(P[0].g) === 0 && plies < 400) {
    const mover = P[G.api_turn(P[0].g)], other = P[1 - G.api_turn(P[0].g)];
    const code = G.api_move(mover.g, pick(G.api_move_count(mover.g)));
    const got = new Promise((r) => { other.o.onMove = r; });
    mover.o.sendMove(code, G.api_move_card(code));
    mover.g = G.api_play(mover.g, code);
    const recv = await got;
    const before = G.api_turn(other.g);
    other.g = G.api_play_revealed(other.g, recv);
    if (G.api_turn(other.g) === before) throw new Error("receiver rejected an honest move");
    for (let s = 0; s < G.api_width() ** 2; s++) if (G.api_cell(P[0].g, s) !== G.api_cell(P[1].g, s)) throw new Error("boards diverged");
    plies++;
  }
  console.log("honest game:", plies, "plies, outcome", G.api_outcome(P[0].g), "==", G.api_outcome(P[1].g), "cheats flagged:", cheats);
  a.close(); b.close();
}

// ---- a cheater claims a card it was never dealt
{
  const { a, b, da, starter } = await pair("222222");
  const fake = [...Array(18).keys()].find((c) => !da.mine.includes(c) && c !== da.table);
  const flagged = new Promise((r) => { b.onCheat = r; b.onMove = () => r("NOT FLAGGED"); });
  a["send"]({ t: "move", m: G.api_msg_move(fake * 49 * 49 + 42 * 49 + 35), pos: 0, key: "abc123" });
  console.log("cheater:", await flagged);
  a.close(); b.close();
}

// ---- more cheats, each must be flagged by the receiver (decided by the engine's protocol laws)
async function cheat(code, name, act) {
  const { a, b, da } = await pair(code);
  const sent = [], send = a["send"].bind(a);
  a["send"] = (msg) => { sent.push(msg); send(msg); };
  const verdicts = [];
  b.onCheat = (w) => verdicts.push("cheat: " + w);
  b.onMove = () => verdicts.push("accepted");
  await act(a, da, sent);
  await new Promise((r) => setTimeout(r, 500));
  console.log(name + ":", verdicts.join(", "));
  a.close(); b.close();
  return verdicts;
}
const mv = (card) => G.api_msg_move(card * 49 * 49 + 42 * 49 + 35);
const bad = [];
// a hidden card with no key at all
let v = await cheat("333333", "no proof", (a, da) => a["send"]({ t: "move", m: mv(da.mine[0]) }));
if (v[0] !== "cheat: carta jogada sem prova") bad.push("no proof");
// the real first card, then the very same message again (replaying a key already used)
v = await cheat("444444", "replayed key", async (a, da, sent) => { a.sendMove(da.mine[0] * 49 * 49 + 42 * 49 + 35, da.mine[0]); await new Promise((r) => setTimeout(r, 300)); a["send"](sent.at(-1)); });
if (v[0] !== "accepted" || !String(v[1]).startsWith("cheat")) bad.push("replayed key");
// the second card proven with the first card's key
v = await cheat("555555", "wrong key", async (a, da, sent) => {
  a.sendMove(da.mine[0] * 49 * 49 + 42 * 49 + 35, da.mine[0]);
  const proofOfFirst = sent.at(-1);
  await new Promise((r) => setTimeout(r, 300));
  a["send"]({ ...proofOfFirst, m: mv(da.mine[1]) });
});
if (v[0] !== "accepted" || !String(v[1]).startsWith("cheat")) bad.push("wrong key");
// ---- out of order or forged setup messages
async function raw(code) {
  const a = await run(Session.open(URL, code, true));
  const b = await run(Session.open(URL, code, false));
  await Promise.all([run(a.waitPeer()), run(b.waitPeer())]);
  const flags = [];
  b.onCheat = (w) => flags.push(w);
  return { a, b, flags };
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
{
  // a move before the deal
  const { a, b, flags } = await raw("666666");
  a["send"]({ t: "move", m: G.api_msg_move(0) }); await sleep(400);
  console.log("move before the deal:", flags.join(", ") || "NOT FLAGGED");
  if (flags[0] !== "mensagem fora de ordem") bad.push("move before the deal");
  a.close(); b.close();
}
{
  // a setup message sent twice: the deal finishes, then the leftover copy is caught
  const { a, b, flags } = await raw("777777");
  const send = a["send"].bind(a);
  a["send"] = (msg) => { send(msg); if (msg.t === "d1") send(msg); };
  await Promise.all([run(a.coin(1)), run(b.coin(0))]);
  await Promise.all([run(a.deal()), run(b.deal())]); await sleep(300);
  console.log("repeated setup message:", flags.join(", ") || "NOT FLAGGED");
  if (flags[0] !== "mensagem fora de ordem") bad.push("repeated setup message");
  a.close(); b.close();
}
{
  // a coin revealed differently from its commitment
  const { a, b } = await raw("888888");
  const send = a["send"].bind(a);
  a["send"] = (msg) => send(msg.t === "reveal" ? { ...msg, n: 1 - msg.n } : msg);
  const exit = await Promise.all([Effect.runPromiseExit(a.coin(1)), Effect.runPromiseExit(b.coin(0))]);
  const caught = exit[1]._tag === "Failure" && JSON.stringify(exit[1].cause).includes("Cheat");
  console.log("forged coin:", caught ? "cheat caught" : "NOT FLAGGED");
  if (!caught) bad.push("forged coin");
  a.close(); b.close();
}
console.log(bad.length ? "NOT FLAGGED: " + bad.join(", ") : "all cheats flagged");
process.exit(bad.length ? 1 : 0);
