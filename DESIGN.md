---
name: Recreio
description: Futebol de botão with cards, played on a lamp-lit felt table.
colors:
  room: "#0f0b08"
  room-glow: "#2c1d11"
  wood: "#3b2212"
  wood-hi: "#5d3519"
  wood-edge: "#1f1108"
  felt: "#1d6a3b"
  felt-deep: "#134d2b"
  card-band: "#12391f"
  chalk: "#f1efe6"
  ink: "#f4efe6"
  ink-dim: "#d4c6ae"
  brass: "#d6a43a"
  brass-hi: "#f2c75c"
  brass-deep: "#9a7322"
  team-blue: "#2453d4"
  team-red: "#d63a3a"
  card: "#f7f5ee"
  card-ink: "#1d140c"
  well: "#0c0b0a"
  error-chalk: "#ffb4a8"
typography:
  display:
    fontFamily: "Big Shoulders Display, Barlow, sans-serif"
    fontSize: "clamp(64px, 19vw, 104px)"
    fontWeight: 900
    lineHeight: 0.86
    letterSpacing: "0.005em"
  headline:
    fontFamily: "Big Shoulders Display, Barlow, sans-serif"
    fontSize: "clamp(44px, 12vw, 60px)"
    fontWeight: 900
    lineHeight: 0.86
    letterSpacing: "0.005em"
  title:
    fontFamily: "Big Shoulders Display, Barlow, sans-serif"
    fontSize: "19px"
    fontWeight: 800
    lineHeight: 1
    letterSpacing: "0.08em"
  numeral:
    fontFamily: "Big Shoulders Display, Barlow, sans-serif"
    fontSize: "30px"
    fontWeight: 900
    lineHeight: 1
    fontFeature: "tnum"
  card-name:
    fontFamily: "Big Shoulders Display, Barlow, sans-serif"
    fontSize: "15px"
    fontWeight: 800
    lineHeight: 1
    letterSpacing: "0.05em"
  body:
    fontFamily: "Barlow, system-ui, sans-serif"
    fontSize: "16px"
    fontWeight: 500
    lineHeight: 1.4
  button:
    fontFamily: "Barlow, system-ui, sans-serif"
    fontSize: "17px"
    fontWeight: 700
    lineHeight: 1
    letterSpacing: "0.01em"
  label:
    fontFamily: "Barlow, system-ui, sans-serif"
    fontSize: "12px"
    fontWeight: 600
    lineHeight: 1
    letterSpacing: "0.06em"
rounded:
  inset: "6px"
  well: "7px"
  chip: "8px"
  segment: "9px"
  control: "10px"
  panel: "12px"
  plaque: "14px"
  round: "50%"
spacing:
  "4": "4px"
  "6": "6px"
  "8": "8px"
  "10": "10px"
  "12": "12px"
  "14": "14px"
  "16": "16px"
  "20": "20px"
components:
  button-primary:
    backgroundColor: "{colors.brass}"
    textColor: "{colors.card-ink}"
    typography: "{typography.button}"
    rounded: "{rounded.control}"
    padding: "0 18px"
    height: "50px"
  button-secondary:
    backgroundColor: "{colors.wood}"
    textColor: "{colors.chalk}"
    typography: "{typography.button}"
    rounded: "{rounded.control}"
    padding: "0 18px"
    height: "50px"
  segmented-option:
    backgroundColor: "{colors.felt}"
    textColor: "{colors.chalk}"
    rounded: "{rounded.segment}"
    height: "44px"
  segmented-option-selected:
    backgroundColor: "{colors.felt}"
    textColor: "{colors.brass-hi}"
    rounded: "{rounded.segment}"
    height: "44px"
  input-room-code:
    backgroundColor: "{colors.well}"
    textColor: "{colors.chalk}"
    rounded: "{rounded.control}"
    padding: "0 14px"
    height: "50px"
  plaque:
    backgroundColor: "{colors.wood}"
    textColor: "{colors.ink}"
    rounded: "{rounded.plaque}"
    padding: "22px 20px 20px"
  placar-cell:
    backgroundColor: "{colors.well}"
    textColor: "{colors.chalk}"
    typography: "{typography.numeral}"
    rounded: "{rounded.well}"
    padding: "6px 8px 5px"
  card-tile:
    backgroundColor: "{colors.card}"
    textColor: "{colors.card-ink}"
    rounded: "{rounded.control}"
    padding: "7px 7px 0"
    width: "100px"
  icon-button:
    backgroundColor: "{colors.room}"
    textColor: "{colors.chalk}"
    rounded: "{rounded.control}"
    size: "44px"
---

# Design System: Recreio

## Overview

**Creative North Star: "The Lamp-Lit Button Table"**

Every surface is a physical object on or around a futebol de botão table: painted felt with chalk lines, a varnished wooden frame, glossy acrylic buttons and a brass-banded goalkeeper block, all under one warm overhead lamp in a dark room. The 3D table (React Three Fiber) is the hero and fills the stage; DOM UI sits around it as more objects from the same room. Menus and dialogs are wooden plaques, the scoreboard is a wooden bar with dark inset wells, cards are thick card-stock tiles whose face is a miniature felt patch.

Density is low and tactile: a few large controls at a time, one status line, one clear next action. Lettering comes in two voices: condensed decal display type for names, numbers and titles, and a plain sturdy sans for everything you read or press. Motion behaves like objects on felt: things decelerate (cubic-bezier(0.16, 1, 0.3, 1)), lift when chosen, slide with friction, and never bounce in place.

The world refuses the flat two-tone chess grid with a side panel. Depth comes from material and light (grain, fibers, inset wells, soft lamp shadow), never from flat cards floating on a blank background.

**Key Characteristics:**
- Materials, not surfaces: wood grain, felt fibers, chalk, card stock, brass, acrylic.
- Brass is the single action and selection color.
- Blue and red belong to the two sides only.
- One warm lamp: dark room, soft drop shadows, top-edge highlights on raised objects.
- Decal display lettering in uppercase; Barlow for reading and pressing.

## Colors

A dim, warm room palette: near-black brown, varnished wood, billiard-felt green, chalk white, with brass as the only lit accent and two team colors.

### Primary
- **Lamp Brass** (brass, with brass-hi and brass-deep): the only action color. Primary buttons (a vertical brass-hi to brass gradient with a brass-deep rim), selected segments (2-3px brass ring), the selected card's lift ring, the lit targets and selection rings on the 3D felt, the goalkeeper's metal band, corner screws, focus outline (brass-hi), text selection, caret, scrollbar thumb, the "start here" help link, and the 20-turn draw-countdown note.

### Secondary
- **Acrylic Blue** (team-blue) and **Acrylic Red** (team-red): the two sides, nothing else. Pieces (clearcoat acrylic), face-down card backs (radial gradient), the opponent dot in the HUD, the placar cell markers.

### Neutral
- **Lamp-Off Room** (room): page background, 3D scene background and fog; the room-light radial gradient lifts the center toward **Room Glow** (room-glow).
- **Varnished Wood** (wood, wood-hi, wood-edge): every plaque, the placar bar, the options sheet and the tip strip, always as a 170deg wood-hi to wood gradient under a grain texture, rimmed with wood-edge.
- **Billiard Felt** (felt, felt-deep): the playing surface, segmented options and card faces, always with a fiber texture. **Printed Band** (card-band) is the deep green name strip at the foot of a card tile.
- **Chalk** (chalk): painted lines on the felt, titles and headings, primary readable text on wood. **Ink** (ink) is the body default; **Dim Ink** (ink-dim) carries ledes, help text, labels and hints.
- **Card Stock** (card) with **Card Ink** (card-ink): card tile faces and dark text on brass.
- **Well** (well): the inset black of placar cells and the room-code input.
- **Error Chalk** (error-chalk): the room-join error message only.

### Named Rules
**The One Brass Rule.** If it can be pressed or is currently chosen, it is brass; nothing else is. In the DOM, the one non-interactive brass element is the draw-countdown note (brass-hi), because it is the clock on the next action; brass never decorates.

**The Two Sides Rule.** Blue and red identify a side and are never used for status, warning, or emphasis.

**The Textured Material Rule.** Wood never appears without grain; felt never appears without fibers. A flat wood or felt fill reads as a form, not the table.

## Typography

**Display Font:** Big Shoulders Display 800/900 (self-hosted via @fontsource, falls back to Barlow)
**Body Font:** Barlow 400-700 (self-hosted via @fontsource, falls back to system-ui)

**Character:** Big Shoulders is the decal lettering stuck on the table and the scoreboard: condensed, heavy, uppercase. Barlow is the plain sturdy voice of the game's instructions and buttons.

### Hierarchy
- **Display** (900, clamp(64px, 19vw, 104px), 0.86, uppercase, chalk): the game title on the menu plaque.
- **Headline** (900, clamp(44px, 12vw, 60px), 0.86, uppercase): plaque titles on secondary screens (how to play, final whistle).
- **Title** (800, 18-19px, 1, 0.08em, uppercase, chalk): group headings inside a plaque and help sections.
- **Numeral** (900, 30px, tabular figures): placar percentages; the room code uses the same face at 44px with 0.16em tracking, the code input at 24px with 0.22em.
- **Card name** (800, 15px, 0.05em, uppercase): card names on the printed band; steps down to 12.5px / 11px for long names and 9.5px on small tiles; 17px on wide screens.
- **Body** (500, 16px, 1.4): ledes (max 40ch), help text (max 60ch), status line at 700 17px.
- **Button** (700, 17px, 1, 0.01em): button labels, sentence case.
- **Label** (600, 12px, 0.06em, uppercase, ink-dim): placar labels and the "Na mesa" slot label.

### Named Rules
**The Decal Rule.** Big Shoulders Display is for names, numbers and titles only, always uppercase except numerals. Anything read as a sentence or pressed as an action is Barlow.

## Layout

Mobile-first, portrait. The app is a fixed full-viewport grid with four rows (top HUD, placar, stage, bottom HUD) inside the safe-area insets. The 3D canvas spans the whole grid behind the HUD; HUD rows sit on top and are centered with max widths (top bar 592px, placar 560px, tip 520px). Plaques are max 420px wide (help 560px) and dock to the bottom of the viewport on phones (16px padding); from 1000px wide they move to the right side, vertically centered (40px / 6vw padding), leaving the table visible.

Spacing is tight and small-stepped (4-20px): 14px between plaque blocks, 10px inside a group, 6px between segments and placar cells, 12px between cards in the tray. Groups inside a plaque are separated by a hairline chalk rule (1px, chalk at 12% alpha), not by boxes.

## Elevation & Depth

Depth is lit, not stacked. One warm spotlight (#ffd6a0) over the table casts real shadows in 3D; ambient and hemisphere light are nearly off, so the room falls to dark. DOM objects echo the same lamp: a soft two-layer drop shadow under raised objects, a faint warm highlight on their top edge, and inset shadows for anything recessed.

### Shadow Vocabulary
- **Lamp drop** (`box-shadow: 0 12px 28px rgba(0,0,0,0.5), 0 2px 5px rgba(0,0,0,0.45)`): plaques, options sheet, card tiles.
- **Bar drop** (`box-shadow: 0 8px 18px rgba(0,0,0,0.45)`): the placar bar and tip strip.
- **Top-edge highlight** (`inset 0 1px 0 rgba(255,214,170,0.14)` on wood, `rgba(255,246,214,0.55)` on brass): the varnish or metal catching the lamp.
- **Inset well** (`inset 0 2px 6px rgba(0,0,0,0.7-0.8)`): placar cells and the code input.
- **Chosen lift** (`0 0 0 3px brass, 0 22px 30px rgba(0,0,0,0.55)` with translateY(-12px) on cards): selection is a lift plus a brass ring.

### Named Rules
**The One Lamp Rule.** All shadows fall straight down from above, soft and dark. No colored glows, no hard offset shadows, no light coming from the side.

## Shapes

Softly rounded physical objects: plaques 14px, wells and panels 7-12px, controls 10px, segments 9px. Pieces and team dots are circles. Card tiles are 5:7 with 10px corners and a 5px card-stock edge (#a99f86) along the bottom that reads as thickness. Chalk lines on felt are slightly irregular hand strokes, not vector-perfect.

## Components

### Buttons
Tactile, like a brass fitting or a wooden block.
- **Shape:** gently rounded (10px), 50px tall, 18px side padding.
- **Primary:** brass gradient (brass-hi to brass at 60%), brass-deep rim, card-ink label, drop shadow plus a bright top-edge highlight.
- **Secondary:** dark wood gradient, chalk label, faint chalk rim (22% alpha).
- **Hover / Active / Disabled:** brightness 1.08 on hover, 1px press-down on active, 0.45 opacity disabled. Focus is a 2px brass-hi outline at 3px offset everywhere.
- **Link:** underlined ink-dim text (4px offset); the help entry on the menu is brass-hi, 700.
- **Icon button:** 44px square, translucent dark wood fill, chalk inline-SVG icon.

### Segmented options
Felt chips with fibers (44px, 9px corners, black rim). Selected: brass-hi label and a 2px inset brass ring; the felt stays.

### Inputs
The room-code field is a recessed black well (50px, 10px corners, inset shadow) with chalk display digits spaced 0.22em; the placeholder falls back to Barlow in ink-dim. Caret is brass-hi.

### Plaque (signature container)
Every menu, help and final-whistle panel is a wooden plaque: grain over a 170deg wood gradient, wood-edge rim, lamp drop, 14px corners, 22px 20px 20px padding. The options sheet and first-match tip are smaller plaques from the same wood.

### Placar
A wooden bar (6px padding, 12px corners) holding three inset black wells: Azul / Empate / Vermelho, each with a 7px team-colored dot, a 12px uppercase label and a 30px decal numeral.

### Card tile
Card stock face (100px wide, 118px on wide screens; 68px small), a square felt patch with the move drawn in chalk (grid, target square, the piece as a ringed button), and a deep green printed band with the name. Face-down backs are full team-color gradients with a chalk frame and button motif. Hover lifts 3px; chosen lifts 12px with a brass ring. Transitions 0.35s with the felt deceleration curve.

### Table (3D)
Felt with fiber strokes and hand-chalked lines (7x7 grid, center circle, a heavier goal line, a spot on each goalkeeper's home square (the goal), and a white 3D futsal goal with netting standing behind it, its mouth on that square); a clearcoated wood frame with brass screws. Pieces are clearcoat acrylic in team colors with chalk rings; the goalkeeper (goleiro) block carries a metallic brass band. Lit targets are unlit brass rings and dots so they read under any lighting. The last move leaves a fading chalk scuff.

## Do's and Don'ts

### Do:
- **Do** build every new panel as a wooden plaque (grain, 170deg wood gradient, wood-edge rim, lamp drop).
- **Do** mark the next action and the current choice in brass, and only in brass.
- **Do** use Big Shoulders Display uppercase for titles, names and numbers, and Barlow for sentences and button labels.
- **Do** keep texture on materials: grain on wood, fibers on felt, an inset well for anything recessed.
- **Do** decelerate motion with cubic-bezier(0.16, 1, 0.3, 1) and honor prefers-reduced-motion by removing it.
- **Do** keep chalk marks on the felt outside the playable squares unless they are the grid itself; goals are a goal line, a spot and a net in the margin.

### Don't:
- **Don't** use blue or red for anything but the two sides.
- **Don't** add a second accent color or use brass as decoration.
- **Don't** use flat, untextured wood or felt fills.
- **Don't** use hard offset shadows, colored glows or side lighting.
- **Don't** draw chalk shapes (area boxes, arcs) that cross playable squares.
- **Don't** make anything pop or bounce in place.
