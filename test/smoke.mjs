import G from "../engine/game.mjs";
const t0 = performance.now();
let g = G.api_new(12345, 67890);
console.log("starter", G.api_turn(g), "starter api", G.api_starter(0, 1), "cards", [0,1].map(i => G.api_hand(g,0,i)), [0,1].map(i => G.api_hand(g,1,i)), "table", G.api_table(g));
console.log("moves", G.api_move_count(g), "first", G.api_move(g, 0));
let row = ""; for (let sq = 0; sq < 36; sq++) { row += G.api_cell(g, sq); if (sq % 6 == 5) row += "\n"; } console.log(row);
console.log("card 0 steps", Array.from({length: G.api_card_step_count(0)}, (_, i) => G.api_card_step(0, i)));
console.log("setup ms", (performance.now() - t0).toFixed(1));
