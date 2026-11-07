When using Bend:
- run `bend guide` to learn it
- use `LAWS.bend` to keep important rules
- run `bend PROOF.bend` before committing
- parallelize the code whenever possible

This project:
- after editing `game.bend`, rebuild the engine and the app's module: `bend game.bend -o engine/game.mjs && tools/dts/bend-dts game.bend engine/game.d.mts && tools/dts/bend-dts game.bend app/src/engine/game.ts engine/game.mjs` (build the generator once with `bend tools/dts/main.bend -o tools/dts/bend-dts`)
- the game UI lives in `app/` (React + React Three Fiber); the page never decides a rule, it asks the engine
- `node test/laws.mjs 2000` checks the laws on random games; `node test/online.mjs` needs the relay on :8799
- the relay's decisions live in `relay/relay.bend` (laws in `relay/LAWS.bend`, proofs in `relay/PROOF.bend`); after editing it: `cd relay && bend relay.bend -o src/relay.mjs`; `node test/relay.mjs` checks it over `wrangler dev` on :8799
- `cd app && npm run test:table` (with `npm run dev` running) checks in Brave that the 3D table shows exactly the engine's board over 3 matches in a row
