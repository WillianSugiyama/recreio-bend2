// Type-level check of the generated web/game.d.mts: right uses compile, wrong ones must not.
// run: npx -y -p typescript@5 tsc --noEmit --strict --module nodenext --moduleResolution nodenext --target es2022 test/types-check.ts
import G, { type Game } from "../engine/game.mjs";

const g: Game = G.api_new(1, 2);
const next: Game = G.api_play(g, G.api_move(g, 0));
const name: string = G.api_card_name(G.api_hand(next, 0, 0));
const winner: number = G.api_outcome(next);

// @ts-expect-error a number is not a game
G.api_play(42, 0);
// @ts-expect-error a game is opaque: TS cannot look inside
next.pieces;
// @ts-expect-error card names are strings, not numbers
const n: number = G.api_card_name(0);
// @ts-expect-error only the api_* functions are public
G.apply(g, 0);

export { name, winner, n };

// unions: TS can switch on the constructor, and forgetting a case is an error
const o = G.api_outcome_of(next);
function describe(o: import("../engine/game.mjs").Outcome): string {
  switch (o.$) {
    case "Ongoing": return "playing";
    case "Winner": return o.side.$ === "Blue" ? "blue won" : "red won";
    case "Draw": return "draw";
  }
}
// @ts-expect-error "Tie" is not a constructor of Outcome
const bad: import("../engine/game.mjs").Outcome = { $: "Tie" };
const c = G.api_chances_of(next, 0);
const total: number = c.blue + c.red + c.draws;
export { o, describe, bad, total };
