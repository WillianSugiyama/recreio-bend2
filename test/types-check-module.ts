// The same engine imported as one TypeScript module (web/game.ts): types and code in one file.
import G, { type Game, type Outcome } from "../app/src/engine/game.ts";
const g: Game = G.api_new(1, 2);
const o: Outcome = G.api_outcome_of(G.api_play(g, G.api_move(g, 0)));
// @ts-expect-error a game is opaque here too
g.pieces;
console.log("game.ts runs:", JSON.stringify(o), G.api_card_name(0));
