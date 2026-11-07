// The table shows the game: in Brave, against the dev server, plays 3 matches in a row ("Jogar de
// novo") and after every turn compares the buttons actually visible in the 3D scene with the
// engine's board. Usage: npm run test:table -- [url]  (dev server: npm run dev)
import { chromium } from "playwright-core";
const URL = process.argv[2] ?? "http://127.0.0.1:5173/";
const browser = await chromium.launch({ executablePath: "/Applications/Brave Browser.app/Contents/MacOS/Brave Browser", args: ["--use-angle=metal", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 390, height: 844 } });
await page.addInitScript(() => localStorage.setItem("recreio.tour.done", "1"));
const errors = []; page.on("pageerror", (e) => errors.push(String(e)));
await page.goto(URL); await page.waitForTimeout(1500);

const compare = () => page.evaluate(() => {
  const G = window.__G, g = window.__match.getMatch().g;
  const want = [];
  for (let sq = 0; sq < 49; sq++) { const c = G.api_cell(g, sq); if (c) want.push(`${sq}:${c <= 2 ? 0 : 1}:${c % 2 === 0}`); }
  const got = window.__drawn().map((d) => `${d.sq}:${d.owner}:${d.teacher}`);
  want.sort(); got.sort();
  return { ok: want.join() === got.join(), want: want.length, got: got.length, missing: want.filter((x) => !got.includes(x)), extra: got.filter((x) => !want.includes(x)) };
});

let checks = 0, captures = 0;
const fail = [];
for (let game = 0; game < 3; game++) {
  await page.click(game ? "text=Jogar de novo" : "text=Jogar contra o bot");
  for (let i = 0; i < 400; i++) {
    const st = await page.evaluate(() => { const s = window.__match.getMatch(); return { over: !!s.over, mine: window.__match.myMoves().length > 0 }; });
    if (st.over) break;
    if (!st.mine) { await page.waitForTimeout(150); continue; }
    await page.waitForTimeout(1800); // let moves and knock-offs finish
    const r = await compare(); checks++;
    if (!r.ok) fail.push({ game: game + 1, ...r });
    captures += await page.evaluate(() => {
      const M = window.__match, s = M.getMatch(), ms = M.myMoves();
      const occ = new Set(s.pieces.filter((p) => p.alive).map((p) => p.sq));
      const m = ms.find((x) => occ.has(x.to)) ?? ms[Math.floor(Math.random() * ms.length)];
      M.pickCard(m.card); M.clickSquare(m.from); M.clickSquare(m.to);
      return occ.has(m.to) ? 1 : 0;
    });
  }
  await page.waitForSelector(".whistle");
  await page.waitForTimeout(1800);
}
console.log(`${checks} checks over 3 matches, ${captures} captures by me`);
console.log(fail.length ? "TABLE DIFFERS FROM ENGINE:\n" + JSON.stringify(fail.slice(0, 5), null, 1) : "table always matched the engine");
console.log("errors:", errors.length ? errors : "none");
await browser.close();
process.exit(fail.length || errors.length ? 1 : 0);
