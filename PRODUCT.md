# Product

<!-- impeccable:product-schema 1 -->

## Platform

web

## Stack

Delegated: React + React Three Fiber (Three.js) for the board, React DOM for menus and cards, TypeScript, Vite build, Effect for the online session. The rules engine is `game.bend`, compiled to `web/game.ts` (types + code) by `tools/dts`. Hosted as static files on Cloudflare Pages; the relay is a Cloudflare Worker (`relay/`).
Chosen because the user asked for visual depth and the feel of a real game (2026: PixiJS/Phaser are the 2D picks, Three.js/R3F the 3D one).

## Users

Adult friends playing casual matches, on phone or computer, either against the bot (Fácil/Médio/Difícil) or against each other online with a 6-digit room code.

## Product Purpose

Recreio is a two-player abstract board game on a 7x7 board: each side has 6 students (alunos) and 1 goalkeeper (goleiro), and every move comes from one of the player's two cards. Success: a match that feels like a real, tactile board game, quick to start, and fair (hidden cards stay hidden, nobody can cheat).

## Positioning

The rules are a proven engine: they live in `game.bend` with laws in `LAWS.bend` (all 58 proven in `PROOF.bend`, plus 11 for the relay in `relay/PROOF.bend`, and also checked on thousands of random games), and the online card draw is cryptographic (no dealer, every played card carries its proof). The page never decides a rule; it asks the engine.

## Operating Context

- A match: a random draw decides who starts (each side's secret coin, so neither decides alone), each player has 2 secret cards plus 1 card on the table; play a card's move, then swap it with the table card.
- Turn flow on screen: choose a card, then a piece, then the destination.
- Wins: capture the enemy goalkeeper, or put any piece on the enemy goal (the square where their goalkeeper started). Draws: same position 3 times, or 20 turns without a capture.
- Win chances (blue / draw / red) are shown during the game, computed only from what the player can see.

## Capabilities and Constraints

- 18 cards named after football plays (Toque, Tabela, Abertura, Triangulação, Lançamento, Chutão, Drible, Chapéu, Pelada, Cruzamento, Enfiada, Bicicleta, Inversão, Recuo, Marcação, Retranca, Arrancada, Contra-ataque); every move is mirrored left/right and vertical moves go both ways; at most 3 squares; no card can trap a side.
- Rules must not change in the UI work; any rule change goes through LAWS.bend first.
- UI language: Portuguese (pt-BR). Mobile first, also desktop. Tested in Brave.
- Undecided: final name (Recreio is provisional), sound.

## Brand Commitments

Name "Recreio" (provisional). Pieces are students (alunos) and a goalkeeper (goleiro, called "professor" before); the 18 cards are named after football plays. In code the goalkeeper is still `teacher`.

## Evidence on Hand

No art, logo, audio or testimonials exist. Do not invent players, reviews or stats.

## Product Principles

- The board is the hero: the game should feel physical, not like a form.
- Never show what the player cannot know (enemy cards stay face down).
- One clear next action at every moment (card, piece, destination).
- Fast to start: from opening the page to the first move in a few taps.
