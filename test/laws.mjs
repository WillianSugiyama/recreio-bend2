// Plays many random games through the compiled rules and checks the laws of LAWS.bend on every move.
import G from "../engine/game.mjs";
const N = Number(process.argv[2] ?? 2000);
let seed = 1;
const rand = n => { seed = (seed * 1103515245 + 12345) >>> 0; return (seed >>> 8) % n; };
// the tap checks draw from their own stream, so the random games stay the same games
let tapSeed = 7;
const tapRand = n => { tapSeed = (tapSeed * 1103515245 + 12345) >>> 0; return (tapSeed >>> 8) % n; };
const W = G.api_width(), CELLS = W * W;
const cells = g => Array.from({ length: CELLS }, (_, s) => G.api_cell(g, s));
const cards = g => [G.api_hand(g, 0, 0), G.api_hand(g, 0, 1), G.api_hand(g, 1, 0), G.api_hand(g, 1, 1), G.api_table(g)];
const fail = [];
const check = (ok, what, ctx) => { if (!ok && fail.length < 20) fail.push(what + " " + JSON.stringify(ctx)); };
const stats = { blue: 0, red: 0, draw: 0, plies: 0, captures: 0, home: 0, teacher: 0, quietDraw: 0, repDraw: 0 };
for (let game = 0; game < N; game++) {
  let g = G.api_new(rand(1 << 30), rand(1 << 30));
  for (let ply = 0; ply < 1000; ply++) {
    const cs = cards(g);
    check(new Set(cs).size === 5 && cs.every(c => c < 18), "always_five_cards/every_deal_is_valid", cs);
    const over = G.api_outcome(g) !== 0, n = G.api_move_count(g);
    if (over) { check(n === 0, "no_moves_after_end", { n }); break; }
    check(n > 0, "never_stuck", { ply });
    const before = cells(g), turn = G.api_turn(g), pieces = before.filter(c => c).length;
    // an illegal move changes nothing
    const bad = 17 * CELLS * CELLS;
    if (!G.api_is_legal(g, bad)) check(G.api_play(g, bad) === g || cells(G.api_play(g, bad)).join() === before.join(), "illegal move changes nothing", {});
    // taps (api_click): only ever a legal move of the player who tapped
    for (let k = 0; k < 4; k++) {
      const me = tapRand(2), c = G.api_click(g, me, tapRand(20), tapRand(2) ? CELLS : tapRand(CELLS), tapRand(CELLS));
      if (c.$ === "Play") check(me === turn && G.api_is_legal(g, G.api_move_code(c.card, c.from, c.to)) === 1, "tap_only_plays_legal_moves", { me, turn, c });
    }
    const code = G.api_move(g, rand(n)), card = G.api_move_card(code), from = G.api_move_from(code), to = G.api_move_to(code);
    const mine = turn === 0 ? [1, 2] : [3, 4], theirs = turn === 0 ? [3, 4] : [1, 2];
    check([G.api_hand(g, turn, 0), G.api_hand(g, turn, 1)].includes(card), "move uses a card in hand", { card });
    check(mine.includes(before[from]), "moves own piece", { from });
    check(!mine.includes(before[to]), "never_lands_on_own_piece", { to });
    const enemy = theirs.includes(before[to]), teacherHit = before[to] === theirs[1];
    const home = to === G.api_home(1 - turn), table = G.api_table(g);
    // selecting the button then tapping its destination plays exactly that move
    const tap = G.api_click(g, turn, card, from, to);
    check(tap.$ === "Play" && G.api_move_code(tap.card, tap.from, tap.to) === code, "tap on selected button's dot plays it", { tap, code });
    const g2 = G.api_play(g, code), after = cells(g2), pieces2 = after.filter(c => c).length;
    check(G.api_turn(g2) === 1 - turn, "turn_alternates", {});
    check(enemy ? pieces2 === pieces - 1 : pieces2 === pieces, enemy ? "landing_on_enemy_captures" : "empty_square_keeps_pieces", { pieces, pieces2 });
    check(G.api_table(g2) === card && [G.api_hand(g2, turn, 0), G.api_hand(g2, turn, 1)].includes(table), "used card goes to table, table card to hand", {});
    const out = G.api_outcome(g2), why = G.api_ending(g2).$;
    const expected = out === 0 ? "Playing" : teacherHit ? "KeeperTaken" : home ? "ReachedGoal" : G.api_quiet(g2) >= 20 ? "Stalled" : "Repeated";
    check(why === expected, "ending_only_when_over / ending matches what happened", { why, expected });
    if (teacherHit || home) { check(out === 1 + turn, "capturing_teacher_wins/reaching_enemy_home_wins", { out }); if (teacherHit) stats.teacher++; else stats.home++; }
    else if (out === 3) { if (G.api_quiet(g2) >= 20) stats.quietDraw++; else stats.repDraw++; }
    else check(out === 0, "draw_only_by_rule / win only by rule", { out });
    if (out === 0) check(G.api_quiet(g2) < 20, "twenty_quiet_turns_draw", {});
    if (enemy) stats.captures++;
    stats.plies++; g = g2;
  }
  const o = G.api_outcome(g);
  check(o !== 0, "game ends", {});
  stats[["", "blue", "red", "draw"][o]]++;
}
console.log(N, "games", JSON.stringify(stats));
console.log(fail.length ? "FAILURES:\n" + fail.join("\n") : "all law checks passed");
// chances and bot timing
let g = G.api_new(42, 4242);
for (let i = 0; i < 6; i++) g = G.api_play(g, G.api_move(g, 0));
let t = performance.now(); const p = G.api_chances(g, 0);
const [b, r, d] = [Math.floor(p / 1e6), Math.floor(p / 1e3) % 1e3, p % 1e3];
console.log("chances blue/red/draw", b, r, d, "sum", b + r + d, "ms", (performance.now() - t).toFixed(0));
for (const lvl of [0, 1, 2]) { t = performance.now(); const m = G.api_bot(g, lvl, 7); console.log("bot level", lvl, "move", m, "legal", G.api_is_legal(g, m), "ms", (performance.now() - t).toFixed(0)); }
