// Generated from game.bend by tools/dts. Do not edit: run it again after changing the engine.
declare const bend: unique symbol;
/** A value owned by the Bend engine: keep it and pass it back, never look inside. */
export type Bend<Name extends string> = { readonly [bend]: Name };
export type Opp = Bend<"Opp">;
export type Game = Bend<"Game">;
export type Held = Bend<"Held">;
export type List<A> =
  | { $: "Nil" }
  | { $: "Con"; head: A; tail: List<A> };
export type Side =
  | { $: "Blue" }
  | { $: "Red" };
export type Outcome =
  | { $: "Ongoing" }
  | { $: "Winner"; side: Side }
  | { $: "Draw" };
export type Chances =
  | { $: "Chances"; blue: number; red: number; draws: number; games: number };
export type Ending =
  | { $: "Playing" }
  | { $: "KeeperTaken" }
  | { $: "ReachedGoal" }
  | { $: "Repeated" }
  | { $: "Stalled" };
export type Click =
  | { $: "Play"; card: number; from: number; to: number }
  | { $: "Select"; sq: number }
  | { $: "Clear" }
  | { $: "Crowded" };
export type Order =
  | { $: "Take" }
  | { $: "Hold" }
  | { $: "Cheat" };
export type Verdict =
  | { $: "Accepted"; opp: Opp }
  | { $: "Rejected"; reason: number };

declare const engine: {
  api_new(blue_key: number, red_key: number): Game;
  /** Online the cards come from the cryptographic draw; 99 marks a card we cannot see. */
  api_new_dealt(starter: number, b0: number, b1: number, r0: number, r1: number, t: number): Game;
  /** Online: who starts, from both players' coins (0 or 1, exchanged with commitments). */
  api_starter(blue_coin: number, red_coin: number): number;
  api_cell(g: Game, sq: number): number;
  api_hand(g: Game, side: number, i: number): number;
  api_table(g: Game): number;
  api_turn(g: Game): number;
  api_outcome(g: Game): number;
  api_quiet(g: Game): number;
  api_move_count(g: Game): number;
  api_move(g: Game, i: number): number;
  api_is_legal(g: Game, code: number): number;
  api_play(g: Game, code: number): Game;
  api_play_revealed(g: Game, code: number): Game;
  api_bot(g: Game, level: number, seed: number): number;
  api_chances(g: Game, viewer: number): number;
  api_card_step_count(id: number): number;
  /** One step of a card for drawing it: (dx + 3) * 8 + (dy + 3), dx > 0 right, dy > 0 forward. */
  api_card_step(id: number, i: number): number;
  /** Messages between players go through these, so the roundtrip law covers what is sent. */
  api_msg_move(code: number): string;
  api_msg_resign(): string;
  /** 0 = not a message, 4294967295 = resign, otherwise the move code + 1. */
  api_msg_read(s: string): number;
  api_invite(room: number): string;
  api_card_name(id: number): string;
  api_deck_never_traps(): number;
  api_width(): number;
  api_home(side: number): number;
  api_move_card(code: number): number;
  api_move_from(code: number): number;
  api_move_to(code: number): number;
  /** How the game stands, as a value TS can switch on (o.$ is "Ongoing", "Winner" or "Draw"). */
  api_outcome_of(g: Game): Outcome;
  /** The chances `viewer` sees, as a record TS can read. */
  api_chances_of(g: Game, viewer: number): Chances;
  /** Why the game ended (e.$ is "Playing", "KeeperTaken", "ReachedGoal", "Repeated" or "Stalled"). */
  api_ending(g: Game): Ending;
  /** What tapping `sq` does for `me` with card `card` picked (99: none) and button `s` selected (49: none). */
  api_click(g: Game, me: number, card: number, s: number, sq: number): Click;
  /** A tap's move, played as the page received it (the tap law covers exactly this move). */
  api_play_move(g: Game, card: number, from: number, to: number): Game;
  api_move_code(card: number, from: number, to: number): number;
  /** The table's tokens: api_token(g, i) = piece code * 64 + square (codes as api_cell). */
  api_token_count(g: Game): number;
  api_token(g: Game, i: number): number;
  api_proto_mine(host: number, i: number): number;
  api_proto_handed(host: number, i: number): number;
  api_opp_start(host: number, table: number): Opp;
  /** They play `card`, with or without a proof (`pos` and the card the page opened there). */
  api_opp_play(o: Opp, card: number, has_proof: number, pos: number, opened: number): Verdict;
  api_opp_i_played(o: Opp, card: number): Opp;
  api_mine_start(host: number, c0: number, c1: number): List<Held>;
  api_mine_pos(hs: List<Held>, card: number): number;
  api_mine_play(hs: List<Held>, card: number): List<Held>;
  api_proto_expected(host: number, step: number): number;
  api_proto_order(host: number, step: number, kind: number): Order;
  api_proto_coin_ok(matches: number, bit: number): number;
};
export default engine;
