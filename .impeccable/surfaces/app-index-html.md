---
version: 1
slug: "app-index-html"
primary_target: "app/index.html"
related_targets: []
---

# Surface: Recreio game (menu, odd-or-even, match, game over)

Mode: experience. Audience: adult friends, casual matches on phone or laptop, vs bot or online by room code.
Job: start fast, read the board at a glance, pick card, piece, destination; feel like a physical table game.
Constraints: rules come only from the engine (game.ts); enemy cards never shown; pt-BR; mobile first.

## Direction contract

THESIS: The board is a futebol de botão table: painted felt, a varnished wooden frame, buttons with real volume under one warm lamp. Refuses the flat two-tone chess grid with a side panel.

OWN-WORLD: Felt green field with chalk-white painted lines (the 7x7 grid, a center circle on row 4, goal-mouth boxes around both teacher homes), a dark varnished wood frame with brass corner screws, a dim room around it. Students are glossy acrylic buttons (blue, red); the teacher is the tall rectangular "goleiro" block with a brass band. Cards are thick card tiles whose face is a miniature felt patch with the move painted in chalk and the name on a printed band. Brass is the only action color. Display type: Big Shoulders Display (decal lettering); UI: Barlow.

STORY: Friends open the page, flip odd-or-even with numbered buttons, and play on a table that looks touchable; the scoreboard (placar) tells the chances; a capture knocks a button off the table.

FIRST VIEWPORT: Match screen, portrait: the table fills the width in a tilted 3D view (camera behind the player, about 40 degrees), opponent's two face-down cards as a thin strip above it, the placar (Azul / Empate / Vermelho) as a wooden scoreboard bar under that strip, your two cards and the table card as tiles below the table, one status line between table and cards. Primary action: tapping a card tile, then a button, then a lit brass target on the felt.

FORM: Mesa de futebol de botão, my top-ranked grounded candidate (#1 on the ordered list). seed:a51084d25f4984fc
Signature interaction: the flick. A moved button slides with friction (exponential ease-out) and a small settle; a captured button is struck off the table edge, tumbling out of view; the last move leaves a faint chalk scuff that fades. Motion grammar: everything decelerates like objects on felt; nothing pops or bounces in place.

FINISH: unreviewed and undocumented is unfinished; this build ends with the finish review, the verdict, DESIGN.md, and every shipping raster carrying its provenance
