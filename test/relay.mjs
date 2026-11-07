// The relay over the local Worker (wrangler dev on :8799): pairing, a full room, forwarding only
// to the other browser, unchanged, and the "left" notice. Usage: node test/relay.mjs [ws-url]
const URL = process.argv[2] ?? "ws://127.0.0.1:8799";
const room = String(100000 + Math.floor(Math.random() * 900000));
const open = () => new Promise((ok, no) => {
  const ws = new WebSocket(`${URL}/room/${room}`), got = [];
  ws.onmessage = (e) => got.push(String(e.data));
  ws.onopen = () => ok({ ws, got });
  ws.onerror = () => no(new Error("refused"));
});
const wait = (ms) => new Promise((r) => setTimeout(r, ms));
const check = (ok, what) => { console.log(ok ? "ok  " : "FAIL", what); if (!ok) process.exitCode = 1; };

const a = await open(); await wait(200);
check(a.got.length === 0, "the first browser waits alone");
const b = await open(); await wait(300);
check(a.got.includes('{"t":"peer"}') && b.got.includes('{"t":"peer"}'), "when the second joins, both hear it");
let third = "accepted"; try { (await open()).ws.close(); } catch { third = "refused"; }
check(third === "refused", "a third browser is refused");
a.got.length = 0; b.got.length = 0;
const text = JSON.stringify({ t: "move", m: "P" + "01".repeat(48), note: "çãé ✓" });
a.ws.send(text); await wait(300);
check(b.got.length === 1 && b.got[0] === text, "a message reaches the other browser, unchanged");
check(a.got.length === 0, "and never comes back to the sender");
a.ws.send("x".repeat(70000)); await wait(300);
check(b.got.length === 1, "a message over 64 KB is dropped");
b.ws.send("oi"); await wait(300);
check(a.got.length === 1 && a.got[0] === "oi", "the second browser's message reaches the first");
a.ws.close(); await wait(400);
check(b.got.at(-1) === '{"t":"left"}', "when one leaves, the other hears it");
b.ws.close();
