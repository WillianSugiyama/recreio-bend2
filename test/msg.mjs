import G from "../web/game.mjs";
const s = G.api_msg_move(5 * 1296 + 31 * 36 + 25);
console.log(typeof s, JSON.stringify(s), "read ->", G.api_msg_read(s), "expected", 5 * 1296 + 31 * 36 + 25 + 1);
console.log("resign", JSON.stringify(G.api_msg_resign()), G.api_msg_read(G.api_msg_resign()));
console.log("garbage", G.api_msg_read("hello"), G.api_msg_read("P1,2"), G.api_msg_read(""));
console.log("invite", JSON.stringify(G.api_invite(482913)));
