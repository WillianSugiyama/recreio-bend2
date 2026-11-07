import type { Game } from "./engine/index.ts";

const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
let next = 0;
const pending = new Map<number, (r: unknown) => void>();
worker.onmessage = ({ data }: MessageEvent<{ id: number; result: unknown }>) => {
  pending.get(data.id)?.(data.result);
  pending.delete(data.id);
};
function ask<T>(msg: object): Promise<T> {
  return new Promise((resolve) => {
    const id = ++next;
    pending.set(id, resolve as (r: unknown) => void);
    worker.postMessage({ id, ...msg });
  });
}

export const rand32 = () => crypto.getRandomValues(new Uint32Array(1))[0];
export const botMove = (game: Game, level: number) => ask<number>({ kind: "bot", game, level, seed: rand32() });
export type Odds = { blue: number; red: number; draws: number };
export const odds = (game: Game, viewer: number) => ask<Odds>({ kind: "chances", game, viewer });
