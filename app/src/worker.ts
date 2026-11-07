// Runs the bot and the win chances off the main thread. Both read only what one player can see:
// the engine functions behind them take that player's view, never the other hand.
import G, { type Game } from "./engine/game.ts";

type Ask = { id: number; kind: "bot"; game: Game; level: number; seed: number } | { id: number; kind: "chances"; game: Game; viewer: number };

self.onmessage = ({ data }: MessageEvent<Ask>) => {
  if (data.kind === "bot") self.postMessage({ id: data.id, result: G.api_bot(data.game, data.level, data.seed) });
  else {
    const c = G.api_chances_of(data.game, data.viewer);
    self.postMessage({ id: data.id, result: { blue: c.blue, red: c.red, draws: c.draws } });
  }
};
