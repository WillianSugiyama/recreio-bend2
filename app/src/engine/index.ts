// The page's door into the rules. Every number here comes from game.ts (compiled from game.bend).
import G, { type Game, type Outcome, type Chances } from "./game.ts";

export { G };
export type { Game, Outcome, Chances };

export const W: number = G.api_width();
export const CELLS = W * W;
export const HOMES: readonly [number, number] = [G.api_home(0), G.api_home(1)];
export const UNKNOWN = 99;

export type Side = 0 | 1;
export type Move = { code: number; card: number; from: number; to: number };

export const decode = (code: number): Move => ({ code, card: G.api_move_card(code), from: G.api_move_from(code), to: G.api_move_to(code) });

/** What stands on a square: null, or its owner and whether it is the teacher. */
export type Cell = { owner: Side; teacher: boolean } | null;
export const cellAt = (g: Game, sq: number): Cell => {
  const c = G.api_cell(g, sq);
  return c === 0 ? null : { owner: c <= 2 ? 0 : 1, teacher: c === 2 || c === 4 };
};

/** A card's steps as [dx, dy], dx > 0 to the right, dy > 0 forward (seen by the player holding it). */
export const cardSteps = (id: number): [number, number][] =>
  Array.from({ length: G.api_card_step_count(id) }, (_, i) => {
    const p = G.api_card_step(id, i);
    return [Math.floor(p / 8) - 3, (p % 8) - 3];
  });
export const cardName = (id: number): string => G.api_card_name(id);
export const hand = (g: Game, side: Side): [number, number] => [G.api_hand(g, side, 0), G.api_hand(g, side, 1)];
