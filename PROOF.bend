import Base
import ./game.bend as G
import ./LAWS.bend as Laws

# Proofs of the laws in LAWS.bend. A law with no def here is still open.

# The checker counts the deck itself.
def Laws.deck_has_18_cards():
  {==}

# The checker computes the longest step of every card.
def Laws.cards_reach_at_most_3():
  {==}

# The game starts with the side odd-or-even chose, whatever the draw.
def L.turn_dealt(+starter: G.Side, +d: G.Deal) -> {G.Game.turn(G.start_dealt(starter, d)) == starter : G.Side}:
  match d:
    case G.Deal{b, r, t}:
      {==}





# Neither coin decides who starts: the other player's coin can still make either side start.
def Laws.blue_cannot_choose_who_starts(blue, side):
  match blue side:
    case G.Secret{True{}, ps} G.Blue{}:
      (G.Secret{True{}, Nil{}}, {==})
    case G.Secret{True{}, ps} G.Red{}:
      (G.Secret{False{}, Nil{}}, {==})
    case G.Secret{False{}, ps} G.Blue{}:
      (G.Secret{False{}, Nil{}}, {==})
    case G.Secret{False{}, ps} G.Red{}:
      (G.Secret{True{}, Nil{}}, {==})

def Laws.red_cannot_choose_who_starts(red, side):
  match red side:
    case G.Secret{True{}, ps} G.Blue{}:
      (G.Secret{True{}, Nil{}}, {==})
    case G.Secret{True{}, ps} G.Red{}:
      (G.Secret{False{}, Nil{}}, {==})
    case G.Secret{False{}, ps} G.Blue{}:
      (G.Secret{False{}, Nil{}}, {==})
    case G.Secret{False{}, ps} G.Red{}:
      (G.Secret{True{}, Nil{}}, {==})

def Laws.starter_moves_first(setup):
  L.turn_dealt(G.Setup.starter(setup), G.Setup.deal(setup))

# No card traps a side: the checker computes, for each card and each of the 49 squares, that the
# card reaches at least 8 squares from there (the closure argument is written next to
# Card.never_traps.go in game.bend). Takes about a minute.
def Laws.cards_never_trap():
  {==}

# A game still going has no ending: `ending` reads the same result that `outcome` reads.
def Laws.ongoing_has_no_ending(setup, moves, playing):
  %Equal.sym(G.Outcome, G.outcome(G.after(setup, moves)), G.Ongoing{}, playing) : {G.ending.of(_, G.after(setup, moves)) == G.Playing{} : G.Ending}
  {==}

# ---------------------------------------------------------------- lemmas about any game
# Most laws talk about `G.after(setup, moves)`, a game reached by real play. Many of them hold for
# every game value, so they are proven once for any `g` and then used on the reached game.

# Comparing a word with itself gives EQ (by induction on the length).
def L.word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, L.word_cmp_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}
        case WCon{False{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, L.word_cmp_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}

# Every number equals itself.
def L.u32_eq_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, L.word_cmp_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# Once the game is over there are no legal moves.
def Laws.no_moves_after_end(setup, moves, move, over):
  %Equal.sym(Bool, G.is_over(G.after(setup, moves)), True{}, over) : {G.Actions.has(G.gen.if_ongoing(_, G.after(setup, moves)), move) == False{} : Bool}
  {==}

# The screen shows the player's own cards and the table card.
def L.view_own(g: G.Game, s: G.Side) -> {G.View.own(G.view(g, s)) == G.own_cards(g, s) : List<&2, U32>}:
  match g s:
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{}:
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{}:
      {==}

def Laws.view_shows_own_cards(setup, moves, side):
  L.view_own(G.after(setup, moves), side)

def L.view_table(g: G.Game, s: G.Side) -> {G.View.table(G.view(g, s)) == G.table_card(g) : U32}:
  match g s:
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{}:
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{}:
      {==}

def Laws.view_shows_table_card(setup, moves, side):
  L.view_table(G.after(setup, moves), side)

# Changing the enemy's cards changes nothing on my screen.
def L.hidden(g: G.Game, s: G.Side, cards: List<&2, U32>) -> {G.view(G.with_enemy_hand(g, s, cards), s) == G.view(g, s) : G.View}:
  match g s:
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{}:
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{}:
      {==}

def Laws.enemy_hand_is_hidden(setup, moves, side, other_cards):
  L.hidden(G.after(setup, moves), side, other_cards)

# A legal move hands the turn to the other side.
def L.apply_turn(g: G.Game, m: G.Action) -> {G.turn_of(G.apply(g, m)) == G.Side.other(G.turn_of(g)) : G.Side}:
  match g m:
    case G.Game{t, ps, b, r, tb, q, h, res} G.Action{c, f, to}:
      {==}

def Laws.turn_alternates(setup, moves, move, legal):
  %Equal.sym(Bool, G.is_legal(G.after(setup, moves), move), True{}, legal) : {G.turn_of(G.play.go(_, G.after(setup, moves), move)) == G.Side.other(G.turn_of(G.after(setup, moves))) : G.Side}
  L.apply_turn(G.after(setup, moves), move)

def L.or_true_r(+x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# A column or row equals itself, and so does a cell.
def L.fin_refl(+f: G.Fin7) -> {Nat.is_eq(G.Fin7.nat(f), G.Fin7.nat(f)) == True{} : Bool}:
  match f:
    case G.F0{}:
      {==}
    case G.F1{}:
      {==}
    case G.F2{}:
      {==}
    case G.F3{}:
      {==}
    case G.F4{}:
      {==}
    case G.F5{}:
      {==}
    case G.F6{}:
      {==}

def L.cell_refl(+x: G.Cell) -> {G.Cell.eq(x, x) == True{} : Bool}:
  match x:
    case G.Cell{c, r}:
      %Equal.sym(Bool, Nat.is_eq(G.Fin7.nat(c), G.Fin7.nat(c)), True{}, L.fin_refl(c)) : {Bool.and(_, Nat.is_eq(G.Fin7.nat(r), G.Fin7.nat(r))) == True{} : Bool}
      L.fin_refl(r)

# Landing on the enemy goalkeeper wins.
def L.won_teacher(+ps: List<&2, G.Piece>, +s: G.Side, +to: G.Cell, e: {Some{to} == G.Pieces.teacher_of(ps, s) : Maybe<&2, G.Cell>}) -> {G.won(ps, s, to) == True{} : Bool}:
  %e : {Bool.or(G.Cell.is(_, to), G.Cell.eq(to, G.Side.home(s))) == True{} : Bool}
  %Equal.sym(Bool, G.Cell.eq(to, to), True{}, L.cell_refl(to)) : {Bool.or(_, G.Cell.eq(to, G.Side.home(s))) == True{} : Bool}
  {==}

# Landing on the enemy goal wins.
def L.won_home(+ps: List<&2, G.Piece>, +s: G.Side, +to: G.Cell, e: {to == G.Side.home(s) : G.Cell}) -> {G.won(ps, s, to) == True{} : Bool}:
  %Equal.sym(G.Cell, to, G.Side.home(s), e) : {G.won(ps, s, _) == True{} : Bool}
  %Equal.sym(Bool, G.Cell.eq(G.Side.home(s), G.Side.home(s)), True{}, L.cell_refl(G.Side.home(s))) : {Bool.or(G.Cell.is(G.Pieces.teacher_of(ps, s), G.Side.home(s)), _) == True{} : Bool}
  L.or_true_r(G.Cell.is(G.Pieces.teacher_of(ps, s), G.Side.home(s)))

# A winning move makes the mover the winner, whatever else happens on that move.
def L.win_wins(+g: G.Game, +m: G.Action, w: {G.won(G.Game.pieces(g), G.Side.other(G.Game.turn(g)), G.to_of(m)) == True{} : Bool}) -> {G.outcome(G.apply(g, m)) == G.Winner{G.turn_of(g)} : G.Outcome}:
  match g m:
    case G.Game{t, ps, b, r, tb, q, h, res} G.Action{c, f, to}:
      %Equal.sym(Bool, G.won(ps, G.Side.other(t), to), True{}, w) : {G.outcome(G.apply.go(_, t, ps, b, r, tb, q, h, c, f, to)) == G.Winner{t} : G.Outcome}
      {==}

def L.teacher_win(+g: G.Game, +m: G.Action, e: {Some{G.to_of(m)} == G.enemy_teacher_square(g) : Maybe<&2, G.Cell>}) -> {G.outcome(G.apply(g, m)) == G.Winner{G.turn_of(g)} : G.Outcome}:
  L.win_wins(g, m, L.won_teacher(G.Game.pieces(g), G.Side.other(G.Game.turn(g)), G.to_of(m), e))

def L.home_win(+g: G.Game, +m: G.Action, e: {G.to_of(m) == G.enemy_home(g) : G.Cell}) -> {G.outcome(G.apply(g, m)) == G.Winner{G.turn_of(g)} : G.Outcome}:
  L.win_wins(g, m, L.won_home(G.Game.pieces(g), G.Side.other(G.Game.turn(g)), G.to_of(m), e))

def Laws.capturing_teacher_wins(setup, moves, move, legal, teacher):
  %Equal.sym(Bool, G.is_legal(G.after(setup, moves), move), True{}, legal) : {G.outcome(G.play.go(_, G.after(setup, moves), move)) == G.Winner{G.turn_of(G.after(setup, moves))} : G.Outcome}
  L.teacher_win(G.after(setup, moves), move, teacher)

def Laws.reaching_enemy_home_wins(setup, moves, move, legal, home):
  %Equal.sym(Bool, G.is_legal(G.after(setup, moves), move), True{}, legal) : {G.outcome(G.play.go(_, G.after(setup, moves), move)) == G.Winner{G.turn_of(G.after(setup, moves))} : G.Outcome}
  L.home_win(G.after(setup, moves), move, home)

# ---------------------------------------------------------------- counting pieces

# False is not True: from such a claim anything follows.
def L.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def L.false_is_not_true(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : L.disc(_)
  Unit{}

def L.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      L.le_refl(p)

# a <= b gives a <= b + 1.
def L.le_succ(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n+0n) == True{} : Bool}, L.false_is_not_true(h))
    case 1n+ap 1n+bp:
      L.le_succ(ap, bp, h)

# Moving a piece keeps the number of pieces.
def L.len_move(+ps: List<&2, G.Piece>, +from: G.Cell, +to: G.Cell) -> {G.Pieces.len(G.Pieces.move(ps, from, to)) == G.Pieces.len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.move(rest, from, to)), G.Pieces.len(rest), L.len_move(rest, from, to)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}

def L.le_remove_go(+hit: Bool, +p: G.Piece, +rest: List<&2, G.Piece>, +n: Nat, ih: {Nat.is_le(G.Pieces.len(rest), n) == True{} : Bool}) -> {Nat.is_le(G.Pieces.len(G.Pieces.capture.go(hit, p, rest)), 1n+n) == True{} : Bool}:
  match hit:
    case True{}:
      L.le_succ(G.Pieces.len(rest), n, ih)
    case False{}:
      ih

# Removing pieces never adds any.
def L.le_capture(+ps: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side) -> {Nat.is_le(G.Pieces.len(G.Pieces.capture(ps, sq, e)), G.Pieces.len(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.le_remove_go(Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e), G.Pieces.len(rest), L.le_capture(rest, sq, e))

def L.apply_le(+g: G.Game, +m: G.Action) -> {Nat.is_le(G.piece_count(G.apply(g, m)), G.piece_count(g)) == True{} : Bool}:
  match g m:
    case G.Game{t, ps, b, r, tb, q, h, res} G.Action{c, f, to}:
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.move(G.Pieces.capture(ps, to, G.Side.other(t)), f, to)), G.Pieces.len(G.Pieces.capture(ps, to, G.Side.other(t))), L.len_move(G.Pieces.capture(ps, to, G.Side.other(t)), f, to)) : {Nat.is_le(_, G.Pieces.len(ps)) == True{} : Bool}
      L.le_capture(ps, to, G.Side.other(t))

def L.go_le(+l: Bool, +g: G.Game, +m: G.Action) -> {Nat.is_le(G.piece_count(G.play.go(l, g, m)), G.piece_count(g)) == True{} : Bool}:
  match l:
    case True{}:
      L.apply_le(g, m)
    case False{}:
      L.le_refl(G.piece_count(g))

def Laws.captured_never_return(setup, moves, move):
  +mv = move
  L.go_le(G.is_legal(G.after(setup, moves), mv), G.after(setup, moves), mv)

# ---------------------------------------------------------------- why the game ended

def L.win_is_over(+b: Bool) -> {G.Ending.is_over(G.ending.win(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def L.draw_is_over(+b: Bool) -> {G.Ending.is_over(G.ending.draw(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def L.ending_over(+o: G.Outcome, +g: G.Game) -> {G.Ending.is_over(G.ending.of(o, g)) == G.Outcome.is_over(o) : Bool}:
  match o:
    case G.Ongoing{}:
      {==}
    case G.Winner{s}:
      L.win_is_over(G.Cell.none(G.Pieces.teacher_of(G.Game.pieces(g), G.Side.other(s))))
    case G.Draw{}:
      L.draw_is_over(Nat.is_ge(G.Game.quiet(g), 20n))

def Laws.ending_only_when_over(setup, moves):
  L.ending_over(G.Game.result(G.after(setup, moves)), G.after(setup, moves))

# ---------------------------------------------------------------- chances on screen

def L.add_zero(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, L.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def L.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), L.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# Counting one more simulated game keeps "blue + red + draws = games".
def L.add_keeps(+c: G.Chances, +o: G.Outcome, h: {G.Chances.total(c) == G.Chances.games(c) : Nat}) -> {G.Chances.total(G.Chances.add(c, o)) == G.Chances.games(G.Chances.add(c, o)) : Nat}:
  match c o:
    case G.Chances{b, r, d, n} G.Winner{G.Blue{}}:
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), d), n, h) : {1n+_ == 1n+n : Nat}
      {==}
    case G.Chances{b, r, d, n} G.Winner{G.Red{}}:
      %Equal.sym(Nat, Nat.add(b, 1n+r), 1n+Nat.add(b, r), L.add_succ(b, r)) : {Nat.add(_, d) == 1n+n : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), d), n, h) : {1n+_ == 1n+n : Nat}
      {==}
    case G.Chances{b, r, d, n} G.Draw{}:
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), 1n+d), 1n+Nat.add(Nat.add(b, r), d), L.add_succ(Nat.add(b, r), d)) : {_ == 1n+n : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), d), n, h) : {1n+_ == 1n+n : Nat}
      {==}
    case G.Chances{b, r, d, n} G.Ongoing{}:
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), 1n+d), 1n+Nat.add(Nat.add(b, r), d), L.add_succ(Nat.add(b, r), d)) : {_ == 1n+n : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(b, r), d), n, h) : {1n+_ == 1n+n : Nat}
      {==}

def L.run_keeps(+n: Nat, +v: G.View, +r: U32, +acc: G.Chances, h: {G.Chances.total(acc) == G.Chances.games(acc) : Nat}) -> {G.Chances.total(G.chances.run(n, v, r, acc)) == G.Chances.games(G.chances.run(n, v, r, acc)) : Nat}:
  match n:
    case 0n:
      h
    case 1n+p:
      +o = G.playout(240n, G.is_over(G.View.guess(v, G.View.sample_enemy(v, r))), G.View.guess(v, G.View.sample_enemy(v, r)), G.rng(r))
      L.run_keeps(p, v, G.rng(G.rng(r)), G.Chances.add(acc, o), L.add_keeps(acc, o, h))

def L.all_keeps(+o: G.Outcome, +n: Nat) -> {G.Chances.total(G.chances.all(o, n)) == G.Chances.games(G.chances.all(o, n)) : Nat}:
  match o:
    case G.Winner{G.Blue{}}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, L.add_zero(n)) : {Nat.add(_, 0n) == n : Nat}
      L.add_zero(n)
    case G.Winner{G.Red{}}:
      L.add_zero(n)
    case G.Draw{}:
      {==}
    case G.Ongoing{}:
      {==}

def L.go_keeps(+over: Bool, +v: G.View, +n: Nat) -> {G.Chances.total(G.chances.go(over, v, n)) == G.Chances.games(G.chances.go(over, v, n)) : Nat}:
  match over:
    case True{}:
      L.all_keeps(G.View.result(v), n)
    case False{}:
      L.run_keeps(n, v, (G.mix(G.View.key(v)) + 1 : U32), G.Chances{0n, 0n, 0n, 0n}, {==})

def Laws.chances_add_up(setup, moves, viewer):
  +v = G.view(G.after(setup, moves), viewer)
  L.go_keeps(G.Outcome.is_over(G.View.result(v)), v, 100n)

# A finished game is certain: the view carries the result, and chances.all counts every game for it.
def L.decided(+g: G.Game, +viewer: G.Side, +w: G.Side, e: {G.outcome(g) == G.Winner{w} : G.Outcome}) -> {G.Chances.wins_of(G.chances(G.view(g, viewer)), w) == G.Chances.games(G.chances(G.view(g, viewer))) : Nat}:
  match g viewer w:
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{} G.Blue{}:
      %Equal.sym(G.Outcome, res, G.Winner{G.Blue{}}, e) : {G.Chances.wins_of(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{})), G.Blue{}) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{}))) : Nat}
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{} G.Red{}:
      %Equal.sym(G.Outcome, res, G.Winner{G.Red{}}, e) : {G.Chances.wins_of(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{})), G.Red{}) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{}))) : Nat}
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{} G.Blue{}:
      %Equal.sym(G.Outcome, res, G.Winner{G.Blue{}}, e) : {G.Chances.wins_of(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{})), G.Blue{}) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{}))) : Nat}
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{} G.Red{}:
      %Equal.sym(G.Outcome, res, G.Winner{G.Red{}}, e) : {G.Chances.wins_of(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{})), G.Red{}) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{}))) : Nat}
      {==}

def Laws.decided_game_is_certain(setup, moves, winner, viewer, won):
  L.decided(G.after(setup, moves), viewer, winner, won)

def L.drawn(+g: G.Game, +viewer: G.Side, e: {G.outcome(g) == G.Draw{} : G.Outcome}) -> {G.Chances.draws(G.chances(G.view(g, viewer))) == G.Chances.games(G.chances(G.view(g, viewer))) : Nat}:
  match g viewer:
    case G.Game{t, p, b, r, tb, q, h, res} G.Blue{}:
      %Equal.sym(G.Outcome, res, G.Draw{}, e) : {G.Chances.draws(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{}))) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Blue{}))) : Nat}
      {==}
    case G.Game{t, p, b, r, tb, q, h, res} G.Red{}:
      %Equal.sym(G.Outcome, res, G.Draw{}, e) : {G.Chances.draws(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{}))) == G.Chances.games(G.chances(G.view(G.Game{t, p, b, r, tb, q, h, _}, G.Red{}))) : Nat}
      {==}

def Laws.drawn_game_is_certain(setup, moves, viewer, drawn):
  L.drawn(G.after(setup, moves), viewer, drawn)

# ---------------------------------------------------------------- messages and invites

def L.bit_roundtrip(+b: Bool) -> {G.Bits.bit(G.Bit.char(b)) == Some{b} : Maybe<&2, Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Reading `n` bits back gives the word that was written (by induction on n).
def L.read_show(+n: Nat, +w: Word(n), +rest: String) -> {G.Bits.read(n, G.Bits.show(n, w, rest)) == Some{w} : Maybe<&2, Word(n)>}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Maybe<&2, Bool>, G.Bits.bit(G.Bit.char(b)), Some{b}, L.bit_roundtrip(b)) : {G.Bits.cons(p, _, G.Bits.read(p, G.Bits.show(p, t, rest))) == Some{WCon{b, t}} : Maybe<&2, Word(1n+p)>}
          %Equal.sym(Maybe<&2, Word(p)>, G.Bits.read(p, G.Bits.show(p, t, rest)), Some{t}, L.read_show(p, t, rest)) : {G.Bits.cons(p, Some{b}, _) == Some{WCon{b, t}} : Maybe<&2, Word(1n+p)>}
          {==}

# Dropping the `n` written characters leaves what came after them.
def L.drop_show(+n: Nat, +w: Word(n), +rest: String) -> {G.Bits.drop(n, G.Bits.show(n, w, rest)) == rest : String}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          L.drop_show(p, t, rest)

def L.of_bits(+x: U32, +rest: String) -> {G.U32.of_bits(G.U32.bits(x, rest)) == Some{x} : Maybe<&2, U32>}:
  match x:
    case U32{w}:
      %Equal.sym(Maybe<&2, Word(32n)>, G.Bits.read(32n, G.Bits.show(32n, w, rest)), Some{w}, L.read_show(32n, w, rest)) : {G.U32.of_word(_) == Some{U32{w}} : Maybe<&2, U32>}
      {==}

def L.drop_bits(+x: U32, +rest: String) -> {G.Bits.drop(32n, G.U32.bits(x, rest)) == rest : String}:
  match x:
    case U32{w}:
      L.drop_show(32n, w, rest)

# A cell's page number reads back to the same cell (49 cells, each computed).
def L.cell_roundtrip(+x: G.Cell) -> {G.Cell.of_u32(G.Cell.u32(x)) == Some{x} : Maybe<&2, G.Cell>}:
  match x:
    case G.Cell{G.F0{}, G.F0{}}:
      {==}
    case G.Cell{G.F0{}, G.F1{}}:
      {==}
    case G.Cell{G.F0{}, G.F2{}}:
      {==}
    case G.Cell{G.F0{}, G.F3{}}:
      {==}
    case G.Cell{G.F0{}, G.F4{}}:
      {==}
    case G.Cell{G.F0{}, G.F5{}}:
      {==}
    case G.Cell{G.F0{}, G.F6{}}:
      {==}
    case G.Cell{G.F1{}, G.F0{}}:
      {==}
    case G.Cell{G.F1{}, G.F1{}}:
      {==}
    case G.Cell{G.F1{}, G.F2{}}:
      {==}
    case G.Cell{G.F1{}, G.F3{}}:
      {==}
    case G.Cell{G.F1{}, G.F4{}}:
      {==}
    case G.Cell{G.F1{}, G.F5{}}:
      {==}
    case G.Cell{G.F1{}, G.F6{}}:
      {==}
    case G.Cell{G.F2{}, G.F0{}}:
      {==}
    case G.Cell{G.F2{}, G.F1{}}:
      {==}
    case G.Cell{G.F2{}, G.F2{}}:
      {==}
    case G.Cell{G.F2{}, G.F3{}}:
      {==}
    case G.Cell{G.F2{}, G.F4{}}:
      {==}
    case G.Cell{G.F2{}, G.F5{}}:
      {==}
    case G.Cell{G.F2{}, G.F6{}}:
      {==}
    case G.Cell{G.F3{}, G.F0{}}:
      {==}
    case G.Cell{G.F3{}, G.F1{}}:
      {==}
    case G.Cell{G.F3{}, G.F2{}}:
      {==}
    case G.Cell{G.F3{}, G.F3{}}:
      {==}
    case G.Cell{G.F3{}, G.F4{}}:
      {==}
    case G.Cell{G.F3{}, G.F5{}}:
      {==}
    case G.Cell{G.F3{}, G.F6{}}:
      {==}
    case G.Cell{G.F4{}, G.F0{}}:
      {==}
    case G.Cell{G.F4{}, G.F1{}}:
      {==}
    case G.Cell{G.F4{}, G.F2{}}:
      {==}
    case G.Cell{G.F4{}, G.F3{}}:
      {==}
    case G.Cell{G.F4{}, G.F4{}}:
      {==}
    case G.Cell{G.F4{}, G.F5{}}:
      {==}
    case G.Cell{G.F4{}, G.F6{}}:
      {==}
    case G.Cell{G.F5{}, G.F0{}}:
      {==}
    case G.Cell{G.F5{}, G.F1{}}:
      {==}
    case G.Cell{G.F5{}, G.F2{}}:
      {==}
    case G.Cell{G.F5{}, G.F3{}}:
      {==}
    case G.Cell{G.F5{}, G.F4{}}:
      {==}
    case G.Cell{G.F5{}, G.F5{}}:
      {==}
    case G.Cell{G.F5{}, G.F6{}}:
      {==}
    case G.Cell{G.F6{}, G.F0{}}:
      {==}
    case G.Cell{G.F6{}, G.F1{}}:
      {==}
    case G.Cell{G.F6{}, G.F2{}}:
      {==}
    case G.Cell{G.F6{}, G.F3{}}:
      {==}
    case G.Cell{G.F6{}, G.F4{}}:
      {==}
    case G.Cell{G.F6{}, G.F5{}}:
      {==}
    case G.Cell{G.F6{}, G.F6{}}:
      {==}

def Laws.invite_code_roundtrip(invite):
  match invite:
    case G.Invite{r}:
      %Equal.sym(Maybe<&2, U32>, G.U32.of_bits(G.U32.bits(r, SNil{})), Some{r}, L.of_bits(r, SNil{})) : {G.Invite.of(_) == Some{G.Invite{r}} : Maybe<G.Invite>}
      {==}

def Laws.message_roundtrip(msg):
  match msg:
    case G.Resign{}:
      {==}
    case G.Played{G.Action{c, f, t}}:
      +b3 = G.U32.bits(G.Cell.u32(t), SNil{})
      +b2 = G.U32.bits(G.Cell.u32(f), b3)
      +b1 = G.U32.bits(c, b2)
      %Equal.sym(String, G.Bits.drop(32n, b1), b2, L.drop_bits(c, b2)) : {G.Message.played(G.U32.of_bits(b1), G.Cell.of_maybe(G.U32.of_bits(_)), G.Cell.of_maybe(G.U32.of_bits(G.Bits.drop(32n, _)))) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(String, G.Bits.drop(32n, b2), b3, L.drop_bits(G.Cell.u32(f), b3)) : {G.Message.played(G.U32.of_bits(b1), G.Cell.of_maybe(G.U32.of_bits(b2)), G.Cell.of_maybe(G.U32.of_bits(_))) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(Maybe<&2, U32>, G.U32.of_bits(b1), Some{c}, L.of_bits(c, b2)) : {G.Message.played(_, G.Cell.of_maybe(G.U32.of_bits(b2)), G.Cell.of_maybe(G.U32.of_bits(b3))) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(Maybe<&2, U32>, G.U32.of_bits(b2), Some{G.Cell.u32(f)}, L.of_bits(G.Cell.u32(f), b3)) : {G.Message.played(Some{c}, G.Cell.of_maybe(_), G.Cell.of_maybe(G.U32.of_bits(b3))) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(Maybe<&2, U32>, G.U32.of_bits(b3), Some{G.Cell.u32(t)}, L.of_bits(G.Cell.u32(t), SNil{})) : {G.Message.played(Some{c}, G.Cell.of_u32(G.Cell.u32(f)), G.Cell.of_maybe(_)) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(Maybe<&2, G.Cell>, G.Cell.of_u32(G.Cell.u32(f)), Some{f}, L.cell_roundtrip(f)) : {G.Message.played(Some{c}, _, G.Cell.of_u32(G.Cell.u32(t))) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      %Equal.sym(Maybe<&2, G.Cell>, G.Cell.of_u32(G.Cell.u32(t)), Some{t}, L.cell_roundtrip(t)) : {G.Message.played(Some{c}, Some{f}, _) == Some{G.Played{G.Action{c, f, t}}} : Maybe<G.Message>}
      {==}

# ---------------------------------------------------------------- equal numbers are equal

# From "two bits, then the rest, compare EQ": the bits are equal, and so is the rest.
def L.fin_bits(+a: Bool, +b: Bool, +c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(a, b, c)) == True{} : Bool}) -> {a == b : Bool}:
  match a b c:
    case _ _ LT{}:
      Empty.absurd({a == b : Bool}, L.false_is_not_true(h))
    case _ _ GT{}:
      Empty.absurd({a == b : Bool}, L.false_is_not_true(h))
    case False{} False{} EQ{}:
      {==}
    case False{} True{} EQ{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_is_not_true(h))
    case True{} False{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_is_not_true(h))
    case True{} True{} EQ{}:
      {==}

def L.fin_rest(+a: Bool, +b: Bool, +c: Cmp, h: {Cmp.is_eq(Word.cmp.fin(a, b, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match a b c:
    case _ _ LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, L.false_is_not_true(h))
    case _ _ GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, L.false_is_not_true(h))
    case False{} False{} EQ{}:
      {==}
    case False{} True{} EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == True{} : Bool}, L.false_is_not_true(h))
    case True{} False{} EQ{}:
      Empty.absurd({Cmp.is_eq(EQ{}) == True{} : Bool}, L.false_is_not_true(h))
    case True{} True{} EQ{}:
      {==}

def L.word_eq(+n: Nat, +x: Word(n), +y: Word(n), +h: {Cmp.is_eq(Word.cmp(n, x, y)) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match x y:
        case WCon{a, xt} WCon{b, yt}:
          %L.fin_bits(a, b, Word.cmp(p, xt, yt), h) : {WCon{a, xt} == WCon{_, yt} : Word(1n+p)}
          %L.word_eq(p, xt, yt, L.fin_rest(a, b, Word.cmp(p, xt, yt), h)) : {WCon{a, xt} == WCon{a, _} : Word(1n+p)}
          {==}

# U32.is_eq says True only for equal numbers.
def L.u32_eq_true(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %L.word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def L.zero_eq(+x: U32, h: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}:
  L.u32_eq_true(x, 0, h)

def L.nat_zero(+x: Nat, h: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, L.false_is_not_true(h))

def L.or_swap(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# ---------------------------------------------------------------- the deck: mirror and vertical by construction

# A sideways pair: mirroring the step swaps which half of the pair matches it.
def L.side_swap(+d: G.Dist, +u: Bool, +dy: Nat, +s: G.Step, +rest: Bool) -> {Bool.or(G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, G.Step.mirror(s)), Bool.or(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, G.Step.mirror(s)), rest)) == Bool.or(G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, s), Bool.or(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, s), rest)) : Bool}:
  match s:
    case G.Step{True{}, sdx, su, sdy}:
      L.or_swap(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, G.Step{True{}, sdx, su, sdy}), G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, G.Step{True{}, sdx, su, sdy}), rest)
    case G.Step{False{}, sdx, su, sdy}:
      L.or_swap(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, G.Step{False{}, sdx, su, sdy}), G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, G.Step{False{}, sdx, su, sdy}), rest)

# Every card's steps answer the same for a step and for its mirror.
def L.mirror_steps(+xs: List<&2, G.Shape>, +s: G.Step) -> {G.Steps.has(G.Shapes.steps(xs), G.Step.mirror(s)) == G.Steps.has(G.Shapes.steps(xs), s) : Bool}:
  match xs s:
    case Nil{} _:
      {==}
    case Con{G.Sideways{d, u, dy}, t} _:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.mirror(s)), G.Steps.has(G.Shapes.steps(t), s), L.mirror_steps(t, s)) : {Bool.or(G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, G.Step.mirror(s)), Bool.or(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, G.Step.mirror(s)), _)) == Bool.or(G.Step.same(G.Step{False{}, G.Dist.nat(d), u, dy}, s), Bool.or(G.Step.same(G.Step{True{}, G.Dist.nat(d), u, dy}, s), G.Steps.has(G.Shapes.steps(t), s))) : Bool}
      L.side_swap(d, u, dy, s, G.Steps.has(G.Shapes.steps(t), s))
    case Con{G.Straight{d}, t} G.Step{sr, sdx, su, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.mirror(G.Step{sr, sdx, su, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, su, sdy}), L.mirror_steps(t, G.Step{sr, sdx, su, sdy})) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(d)}, G.Step.mirror(G.Step{sr, sdx, su, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(d)}, G.Step.mirror(G.Step{sr, sdx, su, sdy})), _)) == G.Steps.has(G.Shapes.steps(Con{G.Straight{d}, t}), G.Step{sr, sdx, su, sdy}) : Bool}
      {==}

def L.card_mirror(+c: G.CardDef, +s: G.Step) -> {G.card_has(G.Card.make(c), G.Step.mirror(s)) == G.card_has(G.Card.make(c), s) : Bool}:
  match c:
    case G.CardDef{i, n, sh}:
      L.mirror_steps(sh, s)

def Laws.cards_mirror_left_right(i, in_deck, step, has):
  +c = G.CardDefs.nth(G.deck_defs(), i)
  Equal.trans(Bool, G.card_has(G.Card.make(c), G.Step.mirror(step)), G.card_has(G.Card.make(c), step), True{}, L.card_mirror(c, step), has)

# Every card's steps answer the same for a vertical step and for it flipped: straight shapes come
# up AND down, and sideways shapes never match a vertical step (they move 1 to 3 squares sideways).
def L.flip_steps(+xs: List<&2, G.Shape>, +s: G.Step, v: {G.Step.is_vertical(s) == True{} : Bool}) -> {G.Steps.has(G.Shapes.steps(xs), G.Step.flip(s)) == G.Steps.has(G.Shapes.steps(xs), s) : Bool}:
  match xs s:
    case Nil{} _:
      {==}
    case Con{G.Sideways{G.Sq1{}, u, dy}, t} G.Step{sr, sdx, su, sdy}:
      %Equal.sym(Nat, sdx, 0n, L.nat_zero(sdx, v)) : {G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq1{}, u, dy}, t}), G.Step.flip(G.Step{sr, _, su, sdy})) == G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq1{}, u, dy}, t}), G.Step{sr, _, su, sdy}) : Bool}
      L.flip_steps(t, G.Step{sr, 0n, su, sdy}, {==})
    case Con{G.Sideways{G.Sq2{}, u, dy}, t} G.Step{sr, sdx, su, sdy}:
      %Equal.sym(Nat, sdx, 0n, L.nat_zero(sdx, v)) : {G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq2{}, u, dy}, t}), G.Step.flip(G.Step{sr, _, su, sdy})) == G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq2{}, u, dy}, t}), G.Step{sr, _, su, sdy}) : Bool}
      L.flip_steps(t, G.Step{sr, 0n, su, sdy}, {==})
    case Con{G.Sideways{G.Sq3{}, u, dy}, t} G.Step{sr, sdx, su, sdy}:
      %Equal.sym(Nat, sdx, 0n, L.nat_zero(sdx, v)) : {G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq3{}, u, dy}, t}), G.Step.flip(G.Step{sr, _, su, sdy})) == G.Steps.has(G.Shapes.steps(Con{G.Sideways{G.Sq3{}, u, dy}, t}), G.Step{sr, _, su, sdy}) : Bool}
      L.flip_steps(t, G.Step{sr, 0n, su, sdy}, {==})
    case Con{G.Straight{G.Sq1{}}, t} G.Step{sr, sdx, True{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, True{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, True{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, True{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, True{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))
    case Con{G.Straight{G.Sq1{}}, t} G.Step{sr, sdx, False{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, False{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, False{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, False{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, False{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq1{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))
    case Con{G.Straight{G.Sq2{}}, t} G.Step{sr, sdx, True{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, True{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, True{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, True{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, True{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))
    case Con{G.Straight{G.Sq2{}}, t} G.Step{sr, sdx, False{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, False{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, False{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, False{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, False{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq2{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))
    case Con{G.Straight{G.Sq3{}}, t} G.Step{sr, sdx, True{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, True{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, True{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step.flip(G.Step{sr, sdx, True{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, True{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, True{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, True{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, True{}, sdy}))
    case Con{G.Straight{G.Sq3{}}, t} G.Step{sr, sdx, False{}, sdy}:
      %Equal.sym(Bool, G.Steps.has(G.Shapes.steps(t), G.Step.flip(G.Step{sr, sdx, False{}, sdy})), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}), L.flip_steps(t, G.Step{sr, sdx, False{}, sdy}, v)) : {Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step.flip(G.Step{sr, sdx, False{}, sdy})), _)) == Bool.or(G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, False{}, sdy}), Bool.or(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))) : Bool}
      L.or_swap(G.Step.same(G.Step{True{}, 0n, True{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, False{}, sdy}), G.Step.same(G.Step{True{}, 0n, False{}, G.Dist.nat(G.Sq3{})}, G.Step{sr, sdx, False{}, sdy}), G.Steps.has(G.Shapes.steps(t), G.Step{sr, sdx, False{}, sdy}))

def L.card_flip(+c: G.CardDef, +s: G.Step, v: {G.Step.is_vertical(s) == True{} : Bool}) -> {G.card_has(G.Card.make(c), G.Step.flip(s)) == G.card_has(G.Card.make(c), s) : Bool}:
  match c:
    case G.CardDef{i, n, sh}:
      L.flip_steps(sh, s, v)

def Laws.vertical_goes_both_ways(i, in_deck, step, has, vertical):
  +c = G.CardDefs.nth(G.deck_defs(), i)
  Equal.trans(Bool, G.card_has(G.Card.make(c), G.Step.flip(step)), G.card_has(G.Card.make(c), step), True{}, L.card_flip(c, step, vertical), has)

# ================================================================ never stuck
# The argument (see Card.never_traps.go in game.bend): if the player to move had no legal move,
# the squares of their pieces would be closed under the steps of their first card, so the squares
# reachable from their goalkeeper (at least 8, computed for every square) would all hold their
# pieces, but a side never has more than 7. The pieces below are: booleans and counting, the
# pigeonhole lemma, the walk staying inside a closed set, the move generator, and the invariant
# that every reachable game keeps (valid hands, at most 7 pieces a side, goalkeepers while going).

# ---------------------------------------------------------------- booleans and numbers

def L.and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_is_not_true(h))

def L.and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, L.false_is_not_true(h))

def L.true_is_not_false(h: {True{} == False{} : Bool}) -> Empty:
  L.false_is_not_true(Equal.sym(Bool, True{}, False{}, h))

def L.or_false_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_is_not_false(h))

def L.or_false_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == False{} : Bool}, L.true_is_not_false(h))

def L.le_trans(+a: Nat, +b: Nat, +c: Nat, +x: {Nat.is_le(a, b) == True{} : Bool}, +y: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+cp:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, L.false_is_not_true(x))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, L.false_is_not_true(y))
    case 1n+ap 1n+bp 1n+cp:
      L.le_trans(ap, bp, cp, x, y)

# n >= m + 1 and n <= m cannot both hold.
def L.ge_le_absurd(+n: Nat, +m: Nat, +a: {Nat.is_ge(n, 1n+m) == True{} : Bool}, +b: {Nat.is_le(n, m) == True{} : Bool}) -> Empty:
  match n m:
    case 0n _:
      L.false_is_not_true(a)
    case 1n+np 0n:
      L.false_is_not_true(b)
    case 1n+np 1n+mp:
      L.ge_le_absurd(np, mp, a, b)

def L.nat_eq_sym(+x: Nat, +y: Nat) -> {Nat.is_eq(x, y) == Nat.is_eq(y, x) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      L.nat_eq_sym(xp, yp)

# ---------------------------------------------------------------- cells

def L.fin_eq_true(+x: G.Fin7, +y: G.Fin7, +h: {Nat.is_eq(G.Fin7.nat(x), G.Fin7.nat(y)) == True{} : Bool}) -> {x == y : G.Fin7}:
  match x y:
    case G.F0{} G.F0{}:
      {==}
    case G.F0{} G.F1{}:
      Empty.absurd({G.F0{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F0{} G.F2{}:
      Empty.absurd({G.F0{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F0{} G.F3{}:
      Empty.absurd({G.F0{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F0{} G.F4{}:
      Empty.absurd({G.F0{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F0{} G.F5{}:
      Empty.absurd({G.F0{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F0{} G.F6{}:
      Empty.absurd({G.F0{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F0{}:
      Empty.absurd({G.F1{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F1{}:
      {==}
    case G.F1{} G.F2{}:
      Empty.absurd({G.F1{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F3{}:
      Empty.absurd({G.F1{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F4{}:
      Empty.absurd({G.F1{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F5{}:
      Empty.absurd({G.F1{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F1{} G.F6{}:
      Empty.absurd({G.F1{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F0{}:
      Empty.absurd({G.F2{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F1{}:
      Empty.absurd({G.F2{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F2{}:
      {==}
    case G.F2{} G.F3{}:
      Empty.absurd({G.F2{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F4{}:
      Empty.absurd({G.F2{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F5{}:
      Empty.absurd({G.F2{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F2{} G.F6{}:
      Empty.absurd({G.F2{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F0{}:
      Empty.absurd({G.F3{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F1{}:
      Empty.absurd({G.F3{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F2{}:
      Empty.absurd({G.F3{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F3{}:
      {==}
    case G.F3{} G.F4{}:
      Empty.absurd({G.F3{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F5{}:
      Empty.absurd({G.F3{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F3{} G.F6{}:
      Empty.absurd({G.F3{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F0{}:
      Empty.absurd({G.F4{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F1{}:
      Empty.absurd({G.F4{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F2{}:
      Empty.absurd({G.F4{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F3{}:
      Empty.absurd({G.F4{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F4{}:
      {==}
    case G.F4{} G.F5{}:
      Empty.absurd({G.F4{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F4{} G.F6{}:
      Empty.absurd({G.F4{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F0{}:
      Empty.absurd({G.F5{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F1{}:
      Empty.absurd({G.F5{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F2{}:
      Empty.absurd({G.F5{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F3{}:
      Empty.absurd({G.F5{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F4{}:
      Empty.absurd({G.F5{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F5{} G.F5{}:
      {==}
    case G.F5{} G.F6{}:
      Empty.absurd({G.F5{} == G.F6{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F0{}:
      Empty.absurd({G.F6{} == G.F0{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F1{}:
      Empty.absurd({G.F6{} == G.F1{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F2{}:
      Empty.absurd({G.F6{} == G.F2{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F3{}:
      Empty.absurd({G.F6{} == G.F3{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F4{}:
      Empty.absurd({G.F6{} == G.F4{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F5{}:
      Empty.absurd({G.F6{} == G.F5{} : G.Fin7}, L.false_is_not_true(h))
    case G.F6{} G.F6{}:
      {==}

def L.cell_eq_true(+a: G.Cell, +b: G.Cell, +h: {G.Cell.eq(a, b) == True{} : Bool}) -> {a == b : G.Cell}:
  match a b:
    case G.Cell{ac, ar} G.Cell{bc, br}:
      %L.fin_eq_true(ac, bc, L.and_l(Nat.is_eq(G.Fin7.nat(ac), G.Fin7.nat(bc)), Nat.is_eq(G.Fin7.nat(ar), G.Fin7.nat(br)), h)) : {G.Cell{ac, ar} == G.Cell{_, br} : G.Cell}
      %L.fin_eq_true(ar, br, L.and_r(Nat.is_eq(G.Fin7.nat(ac), G.Fin7.nat(bc)), Nat.is_eq(G.Fin7.nat(ar), G.Fin7.nat(br)), h)) : {G.Cell{ac, ar} == G.Cell{ac, _} : G.Cell}
      {==}

def L.cell_eq_sym(+a: G.Cell, +b: G.Cell) -> {G.Cell.eq(a, b) == G.Cell.eq(b, a) : Bool}:
  match a b:
    case G.Cell{ac, ar} G.Cell{bc, br}:
      %L.nat_eq_sym(G.Fin7.nat(bc), G.Fin7.nat(ac)) : {Bool.and(_, Nat.is_eq(G.Fin7.nat(ar), G.Fin7.nat(br))) == Bool.and(Nat.is_eq(G.Fin7.nat(bc), G.Fin7.nat(ac)), Nat.is_eq(G.Fin7.nat(br), G.Fin7.nat(ar))) : Bool}
      %L.nat_eq_sym(G.Fin7.nat(br), G.Fin7.nat(ar)) : {Bool.and(Nat.is_eq(G.Fin7.nat(bc), G.Fin7.nat(ac)), _) == Bool.and(Nat.is_eq(G.Fin7.nat(bc), G.Fin7.nat(ac)), Nat.is_eq(G.Fin7.nat(br), G.Fin7.nat(ar))) : Bool}
      {==}

# Every cell is one of the 49.
def L.all_has(+q: G.Cell) -> {G.Cells.has(G.Cells.all(), q) == True{} : Bool}:
  match q:
    case G.Cell{G.F0{}, G.F0{}}:
      {==}
    case G.Cell{G.F0{}, G.F1{}}:
      {==}
    case G.Cell{G.F0{}, G.F2{}}:
      {==}
    case G.Cell{G.F0{}, G.F3{}}:
      {==}
    case G.Cell{G.F0{}, G.F4{}}:
      {==}
    case G.Cell{G.F0{}, G.F5{}}:
      {==}
    case G.Cell{G.F0{}, G.F6{}}:
      {==}
    case G.Cell{G.F1{}, G.F0{}}:
      {==}
    case G.Cell{G.F1{}, G.F1{}}:
      {==}
    case G.Cell{G.F1{}, G.F2{}}:
      {==}
    case G.Cell{G.F1{}, G.F3{}}:
      {==}
    case G.Cell{G.F1{}, G.F4{}}:
      {==}
    case G.Cell{G.F1{}, G.F5{}}:
      {==}
    case G.Cell{G.F1{}, G.F6{}}:
      {==}
    case G.Cell{G.F2{}, G.F0{}}:
      {==}
    case G.Cell{G.F2{}, G.F1{}}:
      {==}
    case G.Cell{G.F2{}, G.F2{}}:
      {==}
    case G.Cell{G.F2{}, G.F3{}}:
      {==}
    case G.Cell{G.F2{}, G.F4{}}:
      {==}
    case G.Cell{G.F2{}, G.F5{}}:
      {==}
    case G.Cell{G.F2{}, G.F6{}}:
      {==}
    case G.Cell{G.F3{}, G.F0{}}:
      {==}
    case G.Cell{G.F3{}, G.F1{}}:
      {==}
    case G.Cell{G.F3{}, G.F2{}}:
      {==}
    case G.Cell{G.F3{}, G.F3{}}:
      {==}
    case G.Cell{G.F3{}, G.F4{}}:
      {==}
    case G.Cell{G.F3{}, G.F5{}}:
      {==}
    case G.Cell{G.F3{}, G.F6{}}:
      {==}
    case G.Cell{G.F4{}, G.F0{}}:
      {==}
    case G.Cell{G.F4{}, G.F1{}}:
      {==}
    case G.Cell{G.F4{}, G.F2{}}:
      {==}
    case G.Cell{G.F4{}, G.F3{}}:
      {==}
    case G.Cell{G.F4{}, G.F4{}}:
      {==}
    case G.Cell{G.F4{}, G.F5{}}:
      {==}
    case G.Cell{G.F4{}, G.F6{}}:
      {==}
    case G.Cell{G.F5{}, G.F0{}}:
      {==}
    case G.Cell{G.F5{}, G.F1{}}:
      {==}
    case G.Cell{G.F5{}, G.F2{}}:
      {==}
    case G.Cell{G.F5{}, G.F3{}}:
      {==}
    case G.Cell{G.F5{}, G.F4{}}:
      {==}
    case G.Cell{G.F5{}, G.F5{}}:
      {==}
    case G.Cell{G.F5{}, G.F6{}}:
      {==}
    case G.Cell{G.F6{}, G.F0{}}:
      {==}
    case G.Cell{G.F6{}, G.F1{}}:
      {==}
    case G.Cell{G.F6{}, G.F2{}}:
      {==}
    case G.Cell{G.F6{}, G.F3{}}:
      {==}
    case G.Cell{G.F6{}, G.F4{}}:
      {==}
    case G.Cell{G.F6{}, G.F5{}}:
      {==}
    case G.Cell{G.F6{}, G.F6{}}:
      {==}

# ---------------------------------------------------------------- pigeonhole

def L.distinct(xs: List<&2, G.Cell>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(G.Cells.has(t, h)), L.distinct(t))

def L.subset(xs: List<&2, G.Cell>, +ys: List<&2, G.Cell>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(G.Cells.has(ys, h), L.subset(t, ys))

def L.pick(b: Bool, x: List<&2, G.Cell>, y: List<&2, G.Cell>) -> List<&2, G.Cell>:
  match b:
    case True{}:
      x
    case False{}:
      y

# `ys` without its first `x`.
def L.remove1(ys: List<&2, G.Cell>, +x: G.Cell) -> List<&2, G.Cell>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      L.pick(G.Cell.eq(h, x), t, h <> L.remove1(t, x))

def L.len_remove1.go(+h: G.Cell, +t: List<&2, G.Cell>, +x: G.Cell, +b: Bool, +e: {G.Cell.eq(h, x) == b : Bool}, +m: {G.Cells.has(Con{h, t}, x) == True{} : Bool}, ih: {G.Cells.has(t, x) == True{} : Bool} -> {1n+G.Cells.len(L.remove1(t, x)) == G.Cells.len(t) : Nat}) -> {1n+G.Cells.len(L.remove1(Con{h, t}, x)) == G.Cells.len(Con{h, t}) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Cell.eq(h, x), True{}, e) : {1n+G.Cells.len(L.pick(_, t, h <> L.remove1(t, x))) == 1n+G.Cells.len(t) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, G.Cell.eq(h, x), False{}, e) : {1n+G.Cells.len(L.pick(_, t, h <> L.remove1(t, x))) == 1n+G.Cells.len(t) : Nat}
      +mt = {%e : {Bool.or(_, G.Cells.has(t, x)) == True{} : Bool}; m : {G.Cells.has(t, x) == True{} : Bool}}
      %Equal.sym(Nat, 1n+G.Cells.len(L.remove1(t, x)), G.Cells.len(t), ih(mt)) : {1n+_ == 1n+G.Cells.len(t) : Nat}
      {==}

# Removing a member shortens the list by one.
def L.len_remove1(+ys: List<&2, G.Cell>, +x: G.Cell, +m: {G.Cells.has(ys, x) == True{} : Bool}) -> {1n+G.Cells.len(L.remove1(ys, x)) == G.Cells.len(ys) : Nat}:
  match ys:
    case Nil{}:
      Empty.absurd({1n+0n == 0n : Nat}, L.false_is_not_true(m))
    case Con{h, t}:
      L.len_remove1.go(h, t, x, G.Cell.eq(h, x), {==}, m, mt => L.len_remove1(t, x, mt))

def L.not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_is_not_true(h))

def L.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def L.has_remove1.go(+h: G.Cell, +t: List<&2, G.Cell>, +x: G.Cell, +y: G.Cell, +bx: Bool, +ex: {G.Cell.eq(h, x) == bx : Bool}, +by: Bool, +ey: {G.Cell.eq(h, y) == by : Bool}, +hy: {G.Cells.has(Con{h, t}, y) == True{} : Bool}, +ne: {G.Cell.eq(y, x) == False{} : Bool}, ih: {G.Cells.has(t, y) == True{} : Bool} -> {G.Cells.has(L.remove1(t, x), y) == True{} : Bool}) -> {G.Cells.has(L.remove1(Con{h, t}, x), y) == True{} : Bool}:
  match bx by:
    case True{} True{}:
      +yh = Equal.sym(G.Cell, h, y, L.cell_eq_true(h, y, ey))
      +xh = Equal.sym(G.Cell, h, x, L.cell_eq_true(h, x, ex))
      +hx = {%yh : {G.Cell.eq(_, x) == False{} : Bool}; ne : {G.Cell.eq(h, x) == False{} : Bool}}
      +hh = {%xh : {G.Cell.eq(h, _) == False{} : Bool}; hx : {G.Cell.eq(h, h) == False{} : Bool}}
      Empty.absurd({G.Cells.has(L.remove1(Con{h, t}, x), y) == True{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, G.Cell.eq(h, h), False{}, Equal.sym(Bool, G.Cell.eq(h, h), True{}, L.cell_refl(h)), hh)))
    case True{} False{}:
      %Equal.sym(Bool, G.Cell.eq(h, x), True{}, ex) : {G.Cells.has(L.pick(_, t, h <> L.remove1(t, x)), y) == True{} : Bool}
      {%ey : {Bool.or(_, G.Cells.has(t, y)) == True{} : Bool}; hy : {G.Cells.has(t, y) == True{} : Bool}}
    case False{} True{}:
      %Equal.sym(Bool, G.Cell.eq(h, x), False{}, ex) : {G.Cells.has(L.pick(_, t, h <> L.remove1(t, x)), y) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(h, y), True{}, ey) : {Bool.or(_, G.Cells.has(L.remove1(t, x), y)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, G.Cell.eq(h, x), False{}, ex) : {G.Cells.has(L.pick(_, t, h <> L.remove1(t, x)), y) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(h, y), False{}, ey) : {Bool.or(_, G.Cells.has(L.remove1(t, x), y)) == True{} : Bool}
      ih({%ey : {Bool.or(_, G.Cells.has(t, y)) == True{} : Bool}; hy : {G.Cells.has(t, y) == True{} : Bool}})

# Removing x keeps every other member.
def L.has_remove1(+ys: List<&2, G.Cell>, +x: G.Cell, +y: G.Cell, +hy: {G.Cells.has(ys, y) == True{} : Bool}, +ne: {G.Cell.eq(y, x) == False{} : Bool}) -> {G.Cells.has(L.remove1(ys, x), y) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({G.Cells.has(Nil{}, y) == True{} : Bool}, L.false_is_not_true(hy))
    case Con{h, t}:
      L.has_remove1.go(h, t, x, y, G.Cell.eq(h, x), {==}, G.Cell.eq(h, y), {==}, hy, ne, hy2 => L.has_remove1(t, x, y, hy2, ne))

def L.sub_remove1(+xs: List<&2, G.Cell>, +ys: List<&2, G.Cell>, +x: G.Cell, +s: {L.subset(xs, ys) == True{} : Bool}, +nx: {G.Cells.has(xs, x) == False{} : Bool}) -> {L.subset(xs, L.remove1(ys, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, rest}:
      +ne = L.or_false_l(G.Cell.eq(y, x), G.Cells.has(rest, x), nx)
      +hy = L.and_l(G.Cells.has(ys, y), L.subset(rest, ys), s)
      %Equal.sym(Bool, G.Cells.has(L.remove1(ys, x), y), True{}, L.has_remove1(ys, x, y, hy, ne)) : {Bool.and(_, L.subset(rest, L.remove1(ys, x))) == True{} : Bool}
      L.sub_remove1(rest, ys, x, L.and_r(G.Cells.has(ys, y), L.subset(rest, ys), s), L.or_false_r(G.Cell.eq(y, x), G.Cells.has(rest, x), nx))

# Pigeonhole: a list without repeats, all of whose members are in `ys`, is no longer than `ys`.
def L.pigeon(+xs: List<&2, G.Cell>, +ys: List<&2, G.Cell>, +d: {L.distinct(xs) == True{} : Bool}, +s: {L.subset(xs, ys) == True{} : Bool}) -> {Nat.is_le(G.Cells.len(xs), G.Cells.len(ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.le_zero(G.Cells.len(ys))
    case Con{x, rest}:
      +nx = L.not_true(G.Cells.has(rest, x), L.and_l(Bool.not(G.Cells.has(rest, x)), L.distinct(rest), d))
      +sub = L.sub_remove1(rest, ys, x, L.and_r(G.Cells.has(ys, x), L.subset(rest, ys), s), nx)
      %L.len_remove1(ys, x, L.and_l(G.Cells.has(ys, x), L.subset(rest, ys), s)) : {Nat.is_le(1n+G.Cells.len(rest), _) == True{} : Bool}
      L.pigeon(rest, L.remove1(ys, x), L.and_r(Bool.not(G.Cells.has(rest, x)), L.distinct(rest), d), sub)

# ---------------------------------------------------------------- the walk stays inside a closed set

def L.lands(+S: List<&2, G.Cell>, t: Maybe<&2, G.Cell>) -> Bool:
  match t:
    case None{}:
      True{}
    case Some{c}:
      G.Cells.has(S, c)

# Every step of the card from `sq` leaves the board or lands in S.
def L.steps_ok(+S: List<&2, G.Cell>, sts: List<&2, G.Step>, +side: G.Side, +sq: G.Cell) -> Bool:
  match sts:
    case Nil{}:
      True{}
    case Con{st, rest}:
      Bool.and(L.lands(S, G.Step.target(st, sq, side)), L.steps_ok(S, rest, side, sq))

# Every square of xs passes steps_ok.
def L.all_ok(+S: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, xs: List<&2, G.Cell>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(L.steps_ok(S, sts, side, x), L.all_ok(S, sts, side, t))

def L.all_ok_has.go(+S: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +x: G.Cell, +t: List<&2, G.Cell>, +sq: G.Cell, +b: Bool, +e: {G.Cell.eq(x, sq) == b : Bool}, +h: {L.all_ok(S, sts, side, Con{x, t}) == True{} : Bool}, +m: {G.Cells.has(Con{x, t}, sq) == True{} : Bool}, ih: {L.all_ok(S, sts, side, t) == True{} : Bool} -> {G.Cells.has(t, sq) == True{} : Bool} -> {L.steps_ok(S, sts, side, sq) == True{} : Bool}) -> {L.steps_ok(S, sts, side, sq) == True{} : Bool}:
  match b:
    case True{}:
      %L.cell_eq_true(x, sq, e) : {L.steps_ok(S, sts, side, _) == True{} : Bool}
      L.and_l(L.steps_ok(S, sts, side, x), L.all_ok(S, sts, side, t), h)
    case False{}:
      ih(L.and_r(L.steps_ok(S, sts, side, x), L.all_ok(S, sts, side, t), h), {%e : {Bool.or(_, G.Cells.has(t, sq)) == True{} : Bool}; m : {G.Cells.has(t, sq) == True{} : Bool}})

def L.all_ok_has(+S: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +xs: List<&2, G.Cell>, +h: {L.all_ok(S, sts, side, xs) == True{} : Bool}, +sq: G.Cell, +m: {G.Cells.has(xs, sq) == True{} : Bool}) -> {L.steps_ok(S, sts, side, sq) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({L.steps_ok(S, sts, side, sq) == True{} : Bool}, L.false_is_not_true(m))
    case Con{x, t}:
      L.all_ok_has.go(S, sts, side, x, t, sq, G.Cell.eq(x, sq), {==}, h, m, h2 => m2 => L.all_ok_has(S, sts, side, t, h2, sq, m2))

def L.add_sub.go(+S: List<&2, G.Cell>, +c: G.Cell, +acc: List<&2, G.Cell>, +b: Bool, +e: {G.Cells.has(acc, c) == b : Bool}, +sub: {L.subset(acc, S) == True{} : Bool}, +l: {G.Cells.has(S, c) == True{} : Bool}) -> {L.subset(G.Reach.add.go(G.Cells.has(acc, c), c, acc), S) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Cells.has(acc, c), True{}, e) : {L.subset(G.Reach.add.go(_, c, acc), S) == True{} : Bool}
      sub
    case False{}:
      %Equal.sym(Bool, G.Cells.has(acc, c), False{}, e) : {L.subset(G.Reach.add.go(_, c, acc), S) == True{} : Bool}
      %Equal.sym(Bool, G.Cells.has(S, c), True{}, l) : {Bool.and(_, L.subset(acc, S)) == True{} : Bool}
      sub

def L.add_sub(+S: List<&2, G.Cell>, +t: Maybe<&2, G.Cell>, +acc: List<&2, G.Cell>, +sub: {L.subset(acc, S) == True{} : Bool}, +l: {L.lands(S, t) == True{} : Bool}) -> {L.subset(G.Reach.add(t, acc), S) == True{} : Bool}:
  match t:
    case None{}:
      sub
    case Some{c}:
      L.add_sub.go(S, c, acc, G.Cells.has(acc, c), {==}, sub, l)

def L.add_dis.go(+c: G.Cell, +acc: List<&2, G.Cell>, +b: Bool, +e: {G.Cells.has(acc, c) == b : Bool}, +dis: {L.distinct(acc) == True{} : Bool}) -> {L.distinct(G.Reach.add.go(G.Cells.has(acc, c), c, acc)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Cells.has(acc, c), True{}, e) : {L.distinct(G.Reach.add.go(_, c, acc)) == True{} : Bool}
      dis
    case False{}:
      %Equal.sym(Bool, G.Cells.has(acc, c), False{}, e) : {L.distinct(G.Reach.add.go(_, c, acc)) == True{} : Bool}
      %Equal.sym(Bool, G.Cells.has(acc, c), False{}, e) : {Bool.and(Bool.not(_), L.distinct(acc)) == True{} : Bool}
      dis

def L.add_dis(+t: Maybe<&2, G.Cell>, +acc: List<&2, G.Cell>, +dis: {L.distinct(acc) == True{} : Bool}) -> {L.distinct(G.Reach.add(t, acc)) == True{} : Bool}:
  match t:
    case None{}:
      dis
    case Some{c}:
      L.add_dis.go(c, acc, G.Cells.has(acc, c), {==}, dis)

def L.targets_sub(+S: List<&2, G.Cell>, +sts: List<&2, G.Step>, +sq: G.Cell, +side: G.Side, +acc: List<&2, G.Cell>, +ok: {L.steps_ok(S, sts, side, sq) == True{} : Bool}, +sub: {L.subset(acc, S) == True{} : Bool}) -> {L.subset(G.Reach.targets(sts, sq, side, acc), S) == True{} : Bool}:
  match sts:
    case Nil{}:
      sub
    case Con{st, rest}:
      +l = L.and_l(L.lands(S, G.Step.target(st, sq, side)), L.steps_ok(S, rest, side, sq), ok)
      L.targets_sub(S, rest, sq, side, G.Reach.add(G.Step.target(st, sq, side), acc), L.and_r(L.lands(S, G.Step.target(st, sq, side)), L.steps_ok(S, rest, side, sq), ok), L.add_sub(S, G.Step.target(st, sq, side), acc, sub, l))

def L.targets_dis(+sts: List<&2, G.Step>, +sq: G.Cell, +side: G.Side, +acc: List<&2, G.Cell>, +dis: {L.distinct(acc) == True{} : Bool}) -> {L.distinct(G.Reach.targets(sts, sq, side, acc)) == True{} : Bool}:
  match sts:
    case Nil{}:
      dis
    case Con{st, rest}:
      L.targets_dis(rest, sq, side, G.Reach.add(G.Step.target(st, sq, side), acc), L.add_dis(G.Step.target(st, sq, side), acc, dis))

def L.take_sub(+S: List<&2, G.Cell>, +n: Nat, +xs: List<&2, G.Cell>, +sub: {L.subset(xs, S) == True{} : Bool}) -> {L.subset(G.Cells.take(n, xs), S) == True{} : Bool}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{h, t}:
      %Equal.sym(Bool, G.Cells.has(S, h), True{}, L.and_l(G.Cells.has(S, h), L.subset(t, S), sub)) : {Bool.and(_, L.subset(G.Cells.take(p, t), S)) == True{} : Bool}
      L.take_sub(S, p, t, L.and_r(G.Cells.has(S, h), L.subset(t, S), sub))

def L.append_sub(+S: List<&2, G.Cell>, +a: List<&2, G.Cell>, +b: List<&2, G.Cell>, +sa: {L.subset(a, S) == True{} : Bool}, +sb: {L.subset(b, S) == True{} : Bool}) -> {L.subset(G.Cells.append(a, b), S) == True{} : Bool}:
  match a:
    case Nil{}:
      sb
    case Con{h, t}:
      %Equal.sym(Bool, G.Cells.has(S, h), True{}, L.and_l(G.Cells.has(S, h), L.subset(t, S), sa)) : {Bool.and(_, L.subset(G.Cells.append(t, b), S)) == True{} : Bool}
      L.append_sub(S, t, b, L.and_r(G.Cells.has(S, h), L.subset(t, S), sa), sb)

# If S is closed under the card's steps, exploring from squares of S never leaves S...
def L.walk_sub(+S: List<&2, G.Cell>, +fuel: Nat, +enough: Bool, +queue: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +seen: List<&2, G.Cell>, +cl: {L.all_ok(S, sts, side, S) == True{} : Bool}, +qs: {L.subset(queue, S) == True{} : Bool}, +ss: {L.subset(seen, S) == True{} : Bool}) -> {L.subset(G.Reach.walk(fuel, enough, queue, sts, side, seen), S) == True{} : Bool}:
  match fuel enough queue:
    case 0n _ _:
      ss
    case 1n+f True{} _:
      ss
    case 1n+f False{} Nil{}:
      ss
    case 1n+f False{} Con{sq, rest}:
      +hq = L.and_l(G.Cells.has(S, sq), L.subset(rest, S), qs)
      +fresh = G.Reach.targets(sts, sq, side, seen)
      +fs = L.targets_sub(S, sts, sq, side, seen, L.all_ok_has(S, sts, side, S, cl, sq, hq), ss)
      +n = Nat.sub(G.Cells.len(fresh), G.Cells.len(seen))
      +q2 = L.append_sub(S, rest, G.Cells.take(n, fresh), L.and_r(G.Cells.has(S, sq), L.subset(rest, S), qs), L.take_sub(S, n, fresh, fs))
      L.walk_sub(S, f, Nat.is_ge(G.Cells.len(fresh), 8n), G.Cells.append(rest, G.Cells.take(n, fresh)), sts, side, fresh, cl, q2, fs)

# ...and never repeats a square.
def L.walk_dis(+fuel: Nat, +enough: Bool, +queue: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +seen: List<&2, G.Cell>, +ds: {L.distinct(seen) == True{} : Bool}) -> {L.distinct(G.Reach.walk(fuel, enough, queue, sts, side, seen)) == True{} : Bool}:
  match fuel enough queue:
    case 0n _ _:
      ds
    case 1n+f True{} _:
      ds
    case 1n+f False{} Nil{}:
      ds
    case 1n+f False{} Con{sq, rest}:
      +fresh = G.Reach.targets(sts, sq, side, seen)
      +n = Nat.sub(G.Cells.len(fresh), G.Cells.len(seen))
      L.walk_dis(f, Nat.is_ge(G.Cells.len(fresh), 8n), G.Cells.append(rest, G.Cells.take(n, fresh)), sts, side, fresh, L.targets_dis(sts, sq, side, seen, ds))

# ---------------------------------------------------------------- the move generator

def L.and2(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def L.and3(+a: Bool, +b: Bool, +c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool}) -> {Bool.and(Bool.and(a, b), c) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(Bool.and(_, b), c) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(Bool.and(True{}, _), c) == True{} : Bool}
  hc

def L.not_false(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# The squares of `side`'s pieces.
def L.own(ps: List<&2, G.Piece>, +side: G.Side) -> List<&2, G.Cell>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{G.Piece{s, t, +q}, +rest}:
      L.pick(G.Side.same(s, side), q <> L.own(rest, side), L.own(rest, side))

def L.lands_own(+ps: List<&2, G.Piece>, +side: G.Side, t: Maybe<&2, G.Cell>) -> Bool:
  match t:
    case None{}:
      True{}
    case Some{c}:
      G.Pieces.side_at(ps, c, side)

def L.steps_own(+ps: List<&2, G.Piece>, +side: G.Side, sts: List<&2, G.Step>, +from: G.Cell) -> Bool:
  match sts:
    case Nil{}:
      True{}
    case Con{st, rest}:
      Bool.and(L.lands_own(ps, side, G.Step.target(st, from, side)), L.steps_own(ps, side, rest, from))

def L.pieces_ok(it: List<&2, G.Piece>, +ps: List<&2, G.Piece>, +side: G.Side, +sts: List<&2, G.Step>) -> Bool:
  match it:
    case Nil{}:
      True{}
    case Con{G.Piece{s, _, q}, rest}:
      Bool.and(Bool.or(Bool.not(G.Side.same(s, side)), L.steps_own(ps, side, sts, q)), L.pieces_ok(rest, ps, side, sts))

def L.add_to_nil.go(+to: G.Cell, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +b: Bool, +e: {G.Pieces.side_at(ps, to, side) == b : Bool}, +h: {G.Actions.nonempty(G.gen.add(G.Pieces.side_at(ps, to, side), G.Action{card, from, to}, acc)) == False{} : Bool}) -> {Bool.and(G.Pieces.side_at(ps, to, side), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}:
  match b:
    case True{}:
      +ha = {%e : {G.Actions.nonempty(G.gen.add(_, G.Action{card, from, to}, acc)) == False{} : Bool}; h : {G.Actions.nonempty(acc) == False{} : Bool}}
      L.and2(G.Pieces.side_at(ps, to, side), Bool.not(G.Actions.nonempty(acc)), e, L.not_false(G.Actions.nonempty(acc), ha))
    case False{}:
      Empty.absurd({Bool.and(G.Pieces.side_at(ps, to, side), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}, L.true_is_not_false({%e : {G.Actions.nonempty(G.gen.add(_, G.Action{card, from, to}, acc)) == False{} : Bool}; h : {True{} == False{} : Bool}}))

# If adding a step's move leaves nothing, the step was blocked and nothing was there before.
def L.add_to_nil(+t: Maybe<&2, G.Cell>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +h: {G.Actions.nonempty(G.gen.add_to(t, card, from, side, ps, acc)) == False{} : Bool}) -> {Bool.and(L.lands_own(ps, side, t), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}:
  match t:
    case None{}:
      L.and2(True{}, Bool.not(G.Actions.nonempty(acc)), {==}, L.not_false(G.Actions.nonempty(acc), h))
    case Some{to}:
      L.add_to_nil.go(to, card, from, side, ps, acc, G.Pieces.side_at(ps, to, side), {==}, h)

def L.steps_nil(+sts: List<&2, G.Step>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +h: {G.Actions.nonempty(G.gen.steps(sts, card, from, side, ps, acc)) == False{} : Bool}) -> {Bool.and(L.steps_own(ps, side, sts, from), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}:
  match sts:
    case Nil{}:
      L.and2(True{}, Bool.not(G.Actions.nonempty(acc)), {==}, L.not_false(G.Actions.nonempty(acc), h))
    case Con{st, rest}:
      +t = G.Step.target(st, from, side)
      +acc2 = G.gen.add_to(t, card, from, side, ps, acc)
      +ih = L.steps_nil(rest, card, from, side, ps, acc2, h)
      +h2 = L.not_true(G.Actions.nonempty(acc2), L.and_r(L.steps_own(ps, side, rest, from), Bool.not(G.Actions.nonempty(acc2)), ih))
      +one = L.add_to_nil(t, card, from, side, ps, acc, h2)
      L.and3(L.lands_own(ps, side, t), L.steps_own(ps, side, rest, from), Bool.not(G.Actions.nonempty(acc)), L.and_l(L.lands_own(ps, side, t), Bool.not(G.Actions.nonempty(acc)), one), L.and_l(L.steps_own(ps, side, rest, from), Bool.not(G.Actions.nonempty(acc2)), ih), L.and_r(L.lands_own(ps, side, t), Bool.not(G.Actions.nonempty(acc)), one))

def L.one_nil(+mine: Bool, +sts: List<&2, G.Step>, +card: U32, +q: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +h: {G.Actions.nonempty(G.gen.pieces.one(mine, sts, card, q, side, ps, acc)) == False{} : Bool}) -> {Bool.and(Bool.or(Bool.not(mine), L.steps_own(ps, side, sts, q)), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}:
  match mine:
    case True{}:
      L.steps_nil(sts, card, q, side, ps, acc, h)
    case False{}:
      L.and2(True{}, Bool.not(G.Actions.nonempty(acc)), {==}, L.not_false(G.Actions.nonempty(acc), h))

def L.pieces_nil(+it: List<&2, G.Piece>, +card: U32, +sts: List<&2, G.Step>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +h: {G.Actions.nonempty(G.gen.pieces(it, card, sts, side, ps, acc)) == False{} : Bool}) -> {Bool.and(L.pieces_ok(it, ps, side, sts), Bool.not(G.Actions.nonempty(acc))) == True{} : Bool}:
  match it:
    case Nil{}:
      L.and2(True{}, Bool.not(G.Actions.nonempty(acc)), {==}, L.not_false(G.Actions.nonempty(acc), h))
    case Con{G.Piece{s, t, q}, rest}:
      +mine = G.Side.same(s, side)
      +acc2 = G.gen.pieces.one(mine, sts, card, q, side, ps, acc)
      +ih = L.pieces_nil(rest, card, sts, side, ps, acc2, h)
      +h2 = L.not_true(G.Actions.nonempty(acc2), L.and_r(L.pieces_ok(rest, ps, side, sts), Bool.not(G.Actions.nonempty(acc2)), ih))
      +one = L.one_nil(mine, sts, card, q, side, ps, acc, h2)
      +head = Bool.or(Bool.not(mine), L.steps_own(ps, side, sts, q))
      L.and3(head, L.pieces_ok(rest, ps, side, sts), Bool.not(G.Actions.nonempty(acc)), L.and_l(head, Bool.not(G.Actions.nonempty(acc)), one), L.and_l(L.pieces_ok(rest, ps, side, sts), Bool.not(G.Actions.nonempty(acc2)), ih), L.and_r(head, Bool.not(G.Actions.nonempty(acc)), one))

def L.cards_acc(+hand: List<&2, U32>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +h: {G.Actions.nonempty(G.gen.cards(hand, side, ps, acc)) == False{} : Bool}) -> {G.Actions.nonempty(acc) == False{} : Bool}:
  match hand:
    case Nil{}:
      h
    case Con{c, rest}:
      +acc2 = G.gen.pieces(ps, c, G.card_steps(c), side, ps, acc)
      +h2 = L.cards_acc(rest, side, ps, acc2, h)
      L.not_true(G.Actions.nonempty(acc), L.and_r(L.pieces_ok(ps, ps, side, G.card_steps(c)), Bool.not(G.Actions.nonempty(acc)), L.pieces_nil(ps, c, G.card_steps(c), side, ps, acc, h2)))

# ---- from "blocked by own pieces" to "lands in the set of own squares"

def L.code_side(+s: G.Side, +t: Bool, +side: G.Side, +h: {G.Code.is_side(G.Piece.code(s, t), side) == True{} : Bool}) -> {G.Side.same(s, side) == True{} : Bool}:
  match s t side:
    case G.Blue{} True{} G.Blue{}:
      {==}
    case G.Blue{} True{} G.Red{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Red{}) == True{} : Bool}, L.false_is_not_true(h))
    case G.Blue{} False{} G.Blue{}:
      {==}
    case G.Blue{} False{} G.Red{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Red{}) == True{} : Bool}, L.false_is_not_true(h))
    case G.Red{} True{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Blue{}) == True{} : Bool}, L.false_is_not_true(h))
    case G.Red{} True{} G.Red{}:
      {==}
    case G.Red{} False{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Blue{}) == True{} : Bool}, L.false_is_not_true(h))
    case G.Red{} False{} G.Red{}:
      {==}

def L.side_at_own.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +c: G.Cell, +side: G.Side, +bq: Bool, +eq: {G.Cell.eq(q, c) == bq : Bool}, +bs: Bool, +es: {G.Side.same(s, side) == bs : Bool}, +h: {G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, c, side) == True{} : Bool}, ih: {G.Pieces.side_at(rest, c, side) == True{} : Bool} -> {G.Cells.has(L.own(rest, side), c) == True{} : Bool}) -> {G.Cells.has(L.own(Con{G.Piece{s, t, q}, rest}, side), c) == True{} : Bool}:
  match bq bs:
    case True{} True{}:
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), c) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, c), True{}, eq) : {Bool.or(_, G.Cells.has(L.own(rest, side), c)) == True{} : Bool}
      {==}
    case True{} False{}:
      +hc = {%eq : {G.Code.is_side(G.sel(_, G.Piece.code(s, t), G.Pieces.code_at(rest, c)), side) == True{} : Bool}; h : {G.Code.is_side(G.Piece.code(s, t), side) == True{} : Bool}}
      Empty.absurd({G.Cells.has(L.own(Con{G.Piece{s, t, q}, rest}, side), c) == True{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, G.Side.same(s, side), False{}, Equal.sym(Bool, G.Side.same(s, side), True{}, L.code_side(s, t, side, hc)), es)))
    case False{} True{}:
      +hr = {%eq : {G.Code.is_side(G.sel(_, G.Piece.code(s, t), G.Pieces.code_at(rest, c)), side) == True{} : Bool}; h : {G.Pieces.side_at(rest, c, side) == True{} : Bool}}
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), c) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, c), False{}, eq) : {Bool.or(_, G.Cells.has(L.own(rest, side), c)) == True{} : Bool}
      ih(hr)
    case False{} False{}:
      +hr = {%eq : {G.Code.is_side(G.sel(_, G.Piece.code(s, t), G.Pieces.code_at(rest, c)), side) == True{} : Bool}; h : {G.Pieces.side_at(rest, c, side) == True{} : Bool}}
      %Equal.sym(Bool, G.Side.same(s, side), False{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), c) == True{} : Bool}
      ih(hr)

# A square holding one of `side`'s pieces is among `side`'s squares.
def L.side_at_own(+ps: List<&2, G.Piece>, +c: G.Cell, +side: G.Side, +h: {G.Pieces.side_at(ps, c, side) == True{} : Bool}) -> {G.Cells.has(L.own(ps, side), c) == True{} : Bool}:
  match ps:
    case Nil{}:
      match side:
        case G.Blue{}:
          Empty.absurd({G.Cells.has(Nil{}, c) == True{} : Bool}, L.false_is_not_true(h))
        case G.Red{}:
          Empty.absurd({G.Cells.has(Nil{}, c) == True{} : Bool}, L.false_is_not_true(h))
    case Con{G.Piece{s, t, q}, rest}:
      L.side_at_own.go(s, t, q, rest, c, side, G.Cell.eq(q, c), {==}, G.Side.same(s, side), {==}, h, h2 => L.side_at_own(rest, c, side, h2))

def L.lands_conv(+ps: List<&2, G.Piece>, +side: G.Side, +t: Maybe<&2, G.Cell>, +h: {L.lands_own(ps, side, t) == True{} : Bool}) -> {L.lands(L.own(ps, side), t) == True{} : Bool}:
  match t:
    case None{}:
      {==}
    case Some{c}:
      L.side_at_own(ps, c, side, h)

def L.steps_conv(+ps: List<&2, G.Piece>, +side: G.Side, +sts: List<&2, G.Step>, +from: G.Cell, +h: {L.steps_own(ps, side, sts, from) == True{} : Bool}) -> {L.steps_ok(L.own(ps, side), sts, side, from) == True{} : Bool}:
  match sts:
    case Nil{}:
      {==}
    case Con{st, rest}:
      +t = G.Step.target(st, from, side)
      L.and2(L.lands(L.own(ps, side), t), L.steps_ok(L.own(ps, side), rest, side, from), L.lands_conv(ps, side, t, L.and_l(L.lands_own(ps, side, t), L.steps_own(ps, side, rest, from), h)), L.steps_conv(ps, side, rest, from, L.and_r(L.lands_own(ps, side, t), L.steps_own(ps, side, rest, from), h)))

def L.all_ok_of.go(+s: G.Side, +q: G.Cell, +rest: List<&2, G.Piece>, +ps: List<&2, G.Piece>, +side: G.Side, +sts: List<&2, G.Step>, +b: Bool, +e: {G.Side.same(s, side) == b : Bool}, +h: {Bool.and(Bool.or(Bool.not(G.Side.same(s, side)), L.steps_own(ps, side, sts, q)), L.pieces_ok(rest, ps, side, sts)) == True{} : Bool}, +ih: {L.all_ok(L.own(ps, side), sts, side, L.own(rest, side)) == True{} : Bool}) -> {L.all_ok(L.own(ps, side), sts, side, L.pick(G.Side.same(s, side), q <> L.own(rest, side), L.own(rest, side))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Side.same(s, side), True{}, e) : {L.all_ok(L.own(ps, side), sts, side, L.pick(_, q <> L.own(rest, side), L.own(rest, side))) == True{} : Bool}
      +hq = {%e : {Bool.or(Bool.not(_), L.steps_own(ps, side, sts, q)) == True{} : Bool}; L.and_l(Bool.or(Bool.not(G.Side.same(s, side)), L.steps_own(ps, side, sts, q)), L.pieces_ok(rest, ps, side, sts), h) : {L.steps_own(ps, side, sts, q) == True{} : Bool}}
      L.and2(L.steps_ok(L.own(ps, side), sts, side, q), L.all_ok(L.own(ps, side), sts, side, L.own(rest, side)), L.steps_conv(ps, side, sts, q, hq), ih)
    case False{}:
      %Equal.sym(Bool, G.Side.same(s, side), False{}, e) : {L.all_ok(L.own(ps, side), sts, side, L.pick(_, q <> L.own(rest, side), L.own(rest, side))) == True{} : Bool}
      ih

# Blocked pieces make the set of own squares closed under the card's steps.
def L.all_ok_of(+it: List<&2, G.Piece>, +ps: List<&2, G.Piece>, +side: G.Side, +sts: List<&2, G.Step>, +h: {L.pieces_ok(it, ps, side, sts) == True{} : Bool}) -> {L.all_ok(L.own(ps, side), sts, side, L.own(it, side)) == True{} : Bool}:
  match it:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      +ih = L.all_ok_of(rest, ps, side, sts, L.and_r(Bool.or(Bool.not(G.Side.same(s, side)), L.steps_own(ps, side, sts, q)), L.pieces_ok(rest, ps, side, sts), h))
      L.all_ok_of.go(s, q, rest, ps, side, sts, G.Side.same(s, side), {==}, h, ih)

# ---------------------------------------------------------------- the deck check, for one card and one square

def L.trap_go.go(+cid: U32, +st: List<&2, G.Step>, +t: List<&2, G.Card>, +c: U32, +side: G.Side, +b: Bool, +e: {U32.is_eq(cid, c) == b : Bool}, +h: {Bool.and(Bool.and(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{})), G.Cards.never_trap(t)) == True{} : Bool}, +m: {Bool.or(U32.is_eq(cid, c), G.U32s.has(G.Cards.ids(t), c)) == True{} : Bool}, ih: {G.Cards.never_trap(t) == True{} : Bool} -> {G.U32s.has(G.Cards.ids(t), c) == True{} : Bool} -> {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of(t, c), side) == True{} : Bool}) -> {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of.pick(U32.is_eq(cid, c), st, G.Cards.steps_of(t, c)), side) == True{} : Bool}:
  match side b:
    case G.Blue{} True{}:
      %Equal.sym(Bool, U32.is_eq(cid, c), True{}, e) : {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of.pick(_, st, G.Cards.steps_of(t, c)), G.Blue{}) == True{} : Bool}
      L.and_l(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{}), L.and_l(Bool.and(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{})), G.Cards.never_trap(t), h))
    case G.Red{} True{}:
      %Equal.sym(Bool, U32.is_eq(cid, c), True{}, e) : {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of.pick(_, st, G.Cards.steps_of(t, c)), G.Red{}) == True{} : Bool}
      L.and_r(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{}), L.and_l(Bool.and(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{})), G.Cards.never_trap(t), h))
    case _ False{}:
      %Equal.sym(Bool, U32.is_eq(cid, c), False{}, e) : {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of.pick(_, st, G.Cards.steps_of(t, c)), side) == True{} : Bool}
      ih(L.and_r(Bool.and(G.Card.never_traps.go(G.Cells.all(), st, G.Blue{}), G.Card.never_traps.go(G.Cells.all(), st, G.Red{})), G.Cards.never_trap(t), h), {%e : {Bool.or(_, G.U32s.has(G.Cards.ids(t), c)) == True{} : Bool}; m : {G.U32s.has(G.Cards.ids(t), c) == True{} : Bool}})

# A card from the deck passes the check for both sides.
def L.trap_go(+cs: List<&2, G.Card>, +c: U32, +side: G.Side, +h: {G.Cards.never_trap(cs) == True{} : Bool}, +m: {G.U32s.has(G.Cards.ids(cs), c) == True{} : Bool}) -> {G.Card.never_traps.go(G.Cells.all(), G.Cards.steps_of(cs, c), side) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({G.Card.never_traps.go(G.Cells.all(), Nil{}, side) == True{} : Bool}, L.false_is_not_true(m))
    case Con{G.Card{cid, n, st}, t}:
      L.trap_go.go(cid, st, t, c, side, U32.is_eq(cid, c), {==}, h, m, h2 => m2 => L.trap_go(t, c, side, h2, m2))

def L.reach8(+sts: List<&2, G.Step>, +side: G.Side, +q: G.Cell) -> Bool:
  Nat.is_ge(G.Cells.len(G.Reach.walk(49n, False{}, [q], sts, side, [q])), 8n)

def L.go_has.go(+x: G.Cell, +rest: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +q: G.Cell, +b: Bool, +e: {G.Cell.eq(x, q) == b : Bool}, +h: {G.Card.never_traps.go(Con{x, rest}, sts, side) == True{} : Bool}, +m: {G.Cells.has(Con{x, rest}, q) == True{} : Bool}, ih: {G.Card.never_traps.go(rest, sts, side) == True{} : Bool} -> {G.Cells.has(rest, q) == True{} : Bool} -> {L.reach8(sts, side, q) == True{} : Bool}) -> {L.reach8(sts, side, q) == True{} : Bool}:
  match b:
    case True{}:
      %L.cell_eq_true(x, q, e) : {L.reach8(sts, side, _) == True{} : Bool}
      L.and_l(L.reach8(sts, side, x), G.Card.never_traps.go(rest, sts, side), h)
    case False{}:
      ih(L.and_r(L.reach8(sts, side, x), G.Card.never_traps.go(rest, sts, side), h), {%e : {Bool.or(_, G.Cells.has(rest, q)) == True{} : Bool}; m : {G.Cells.has(rest, q) == True{} : Bool}})

def L.go_has(+sqs: List<&2, G.Cell>, +sts: List<&2, G.Step>, +side: G.Side, +h: {G.Card.never_traps.go(sqs, sts, side) == True{} : Bool}, +q: G.Cell, +m: {G.Cells.has(sqs, q) == True{} : Bool}) -> {L.reach8(sts, side, q) == True{} : Bool}:
  match sqs:
    case Nil{}:
      Empty.absurd({L.reach8(sts, side, q) == True{} : Bool}, L.false_is_not_true(m))
    case Con{x, rest}:
      L.go_has.go(x, rest, sts, side, q, G.Cell.eq(x, q), {==}, h, m, h2 => m2 => L.go_has(rest, sts, side, h2, q, m2))

# From any square, a deck card reaches at least 8 squares (from cards_never_trap).
# The deck check, stated exactly as trap_go reads it.
def L.trap_all() -> {G.Cards.never_trap(G.deck()) == True{} : Bool}:
  {==}

def L.deck_reach8(+c: U32, +side: G.Side, +q: G.Cell, +m: {G.U32s.has(G.Cards.ids(G.deck()), c) == True{} : Bool}) -> {L.reach8(G.card_steps(c), side, q) == True{} : Bool}:
  L.go_has(G.Cells.all(), G.card_steps(c), side, L.trap_go(G.deck(), c, side, L.trap_all(), m), q, L.all_has(q))

# ---------------------------------------------------------------- the contradiction

def L.or_r(+a: Bool, +b: Bool, +hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def L.is_some(m: Maybe<&2, G.Cell>) -> Type:
  match m:
    case Some{_}:
      Unit
    case None{}:
      Empty

def L.none_is_not_some(+c: G.Cell, +e: {None{} == Some{c} : Maybe<&2, G.Cell>}) -> Empty:
  %Equal.sym(Maybe<&2, G.Cell>, None{}, Some{c}, e) : L.is_some(_)
  Unit{}

def L.unsome(m: Maybe<&2, G.Cell>, d: G.Cell) -> G.Cell:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def L.some_inj(+a: G.Cell, +b: G.Cell, +e: {Some{a} == Some{b} : Maybe<&2, G.Cell>}) -> {a == b : G.Cell}:
  Equal.cong(Maybe<&2, G.Cell>, G.Cell, m => L.unsome(m, a), Some{a}, Some{b}, e)

def L.teacher_own.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +side: G.Side, +qk: G.Cell, +bt: Bool, +et: {Bool.and(G.Side.same(s, side), t) == bt : Bool}, +bs: Bool, +es: {G.Side.same(s, side) == bs : Bool}, +hk: {G.Pieces.teacher_of(Con{G.Piece{s, t, q}, rest}, side) == Some{qk} : Maybe<&2, G.Cell>}, ih: {G.Pieces.teacher_of(rest, side) == Some{qk} : Maybe<&2, G.Cell>} -> {G.Cells.has(L.own(rest, side), qk) == True{} : Bool}) -> {G.Cells.has(L.own(Con{G.Piece{s, t, q}, rest}, side), qk) == True{} : Bool}:
  match bt bs:
    case True{} True{}:
      +sq = {%et : {G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, side)) == Some{qk} : Maybe<&2, G.Cell>}; hk : {Some{q} == Some{qk} : Maybe<&2, G.Cell>}}
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), qk) == True{} : Bool}
      %L.some_inj(q, qk, sq) : {Bool.or(G.Cell.eq(q, _), G.Cells.has(L.own(rest, side), _)) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, q), True{}, L.cell_refl(q)) : {Bool.or(_, G.Cells.has(L.own(rest, side), q)) == True{} : Bool}
      {==}
    case True{} False{}:
      Empty.absurd({G.Cells.has(L.own(Con{G.Piece{s, t, q}, rest}, side), qk) == True{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, G.Side.same(s, side), False{}, Equal.sym(Bool, G.Side.same(s, side), True{}, L.and_l(G.Side.same(s, side), t, Equal.trans(Bool, Bool.and(G.Side.same(s, side), t), True{}, True{}, et, {==}))), es)))
    case False{} True{}:
      +hr = {%et : {G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, side)) == Some{qk} : Maybe<&2, G.Cell>}; hk : {G.Pieces.teacher_of(rest, side) == Some{qk} : Maybe<&2, G.Cell>}}
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), qk) == True{} : Bool}
      L.or_r(G.Cell.eq(q, qk), G.Cells.has(L.own(rest, side), qk), ih(hr))
    case False{} False{}:
      +hr = {%et : {G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, side)) == Some{qk} : Maybe<&2, G.Cell>}; hk : {G.Pieces.teacher_of(rest, side) == Some{qk} : Maybe<&2, G.Cell>}}
      %Equal.sym(Bool, G.Side.same(s, side), False{}, es) : {G.Cells.has(L.pick(_, q <> L.own(rest, side), L.own(rest, side)), qk) == True{} : Bool}
      ih(hr)

# The goalkeeper's square is one of its side's squares.
def L.teacher_own(+ps: List<&2, G.Piece>, +side: G.Side, +qk: G.Cell, +hk: {G.Pieces.teacher_of(ps, side) == Some{qk} : Maybe<&2, G.Cell>}) -> {G.Cells.has(L.own(ps, side), qk) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({G.Cells.has(Nil{}, qk) == True{} : Bool}, L.none_is_not_some(qk, hk))
    case Con{G.Piece{s, t, q}, rest}:
      L.teacher_own.go(s, t, q, rest, side, qk, Bool.and(G.Side.same(s, side), t), {==}, G.Side.same(s, side), {==}, hk, h2 => L.teacher_own(rest, side, qk, h2))

# The core: a side with a goalkeeper, at most 7 pieces and a deck card in hand always has a move.
def L.core(+ps: List<&2, G.Piece>, +side: G.Side, +c: U32, +rest: List<&2, U32>, +qk: G.Cell, +hv: {G.U32s.has(G.Cards.ids(G.deck()), c) == True{} : Bool}, +hk: {G.Pieces.teacher_of(ps, side) == Some{qk} : Maybe<&2, G.Cell>}, +hc: {Nat.is_le(G.Cells.len(L.own(ps, side)), 7n) == True{} : Bool}, +hn: {G.Actions.nonempty(G.gen.cards(Con{c, rest}, side, ps, Nil{})) == False{} : Bool}) -> Empty:
  +sts = G.card_steps(c)
  +S = L.own(ps, side)
  +acc0 = G.gen.pieces(ps, c, sts, side, ps, Nil{})
  +h0 = L.cards_acc(rest, side, ps, acc0, hn)
  +pok = L.and_l(L.pieces_ok(ps, ps, side, sts), Bool.not(G.Actions.nonempty(Nil{})), L.pieces_nil(ps, c, sts, side, ps, Nil{}, h0))
  +cl = L.all_ok_of(ps, ps, side, sts, pok)
  +qs = L.and2(G.Cells.has(S, qk), True{}, L.teacher_own(ps, side, qk, hk), {==})
  +W = G.Reach.walk(49n, False{}, [qk], sts, side, [qk])
  +ws = L.walk_sub(S, 49n, False{}, [qk], sts, side, [qk], cl, qs, qs)
  +wd = L.walk_dis(49n, False{}, [qk], sts, side, [qk], {==})
  +le7 = L.le_trans(G.Cells.len(W), G.Cells.len(S), 7n, L.pigeon(W, S, wd, ws), hc)
  L.ge_le_absurd(G.Cells.len(W), 7n, L.deck_reach8(c, side, qk, hv), le7)

# ---------------------------------------------------------------- the invariant: cards

def L.valid(+c: U32) -> Bool:
  G.U32s.has(G.Cards.ids(G.deck()), c)

# A hand is exactly two deck cards.
def L.hand_ok(h: List<&2, U32>) -> Bool:
  match h:
    case Con{a, Con{b, Nil{}}}:
      Bool.and(L.valid(a), L.valid(b))
    case _:
      False{}



def L.hand_has.go(+a: U32, +b: U32, +c: U32, +ba: Bool, +ea: {U32.is_eq(a, c) == ba : Bool}, +bb: Bool, +eb: {U32.is_eq(b, c) == bb : Bool}, +hok: {Bool.and(L.valid(a), L.valid(b)) == True{} : Bool}, +hh: {G.U32s.has(Con{a, Con{b, Nil{}}}, c) == True{} : Bool}) -> {L.valid(c) == True{} : Bool}:
  match ba bb:
    case True{} _:
      %L.u32_eq_true(a, c, ea) : {L.valid(_) == True{} : Bool}
      L.and_l(L.valid(a), L.valid(b), hok)
    case False{} True{}:
      %L.u32_eq_true(b, c, eb) : {L.valid(_) == True{} : Bool}
      L.and_r(L.valid(a), L.valid(b), hok)
    case False{} False{}:
      +h1 = {%ea : {Bool.or(_, G.U32s.has(Con{b, Nil{}}, c)) == True{} : Bool}; hh : {G.U32s.has(Con{b, Nil{}}, c) == True{} : Bool}}
      Empty.absurd({L.valid(c) == True{} : Bool}, L.false_is_not_true({%eb : {Bool.or(_, False{}) == True{} : Bool}; h1 : {False{} == True{} : Bool}}))

# A card in a valid hand is a deck card.
def L.hand_has(+h: List<&2, U32>, +c: U32, +hok: {L.hand_ok(h) == True{} : Bool}, +hh: {G.U32s.has(h, c) == True{} : Bool}) -> {L.valid(c) == True{} : Bool}:
  match h:
    case Nil{}:
      Empty.absurd({L.valid(c) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Nil{}}:
      Empty.absurd({L.valid(c) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Con{b, Nil{}}}:
      L.hand_has.go(a, b, c, U32.is_eq(a, c), {==}, U32.is_eq(b, c), {==}, hok, hh)
    case Con{a, Con{b, Con{d, rest}}}:
      Empty.absurd({L.valid(c) == True{} : Bool}, L.false_is_not_true(hok))

def L.replace_ok.go(+a: U32, +b: U32, +x: U32, +y: U32, +ba: Bool, +ea: {U32.is_eq(a, x) == ba : Bool}, +bb: Bool, +eb: {U32.is_eq(b, x) == bb : Bool}, +hok: {Bool.and(L.valid(a), L.valid(b)) == True{} : Bool}, +hy: {L.valid(y) == True{} : Bool}) -> {L.hand_ok(G.U32s.replace(Con{a, Con{b, Nil{}}}, x, y)) == True{} : Bool}:
  match ba bb:
    case True{} _:
      %Equal.sym(Bool, U32.is_eq(a, x), True{}, ea) : {L.hand_ok(G.U32s.replace.go(_, a, Con{b, Nil{}}, y, G.U32s.replace(Con{b, Nil{}}, x, y))) == True{} : Bool}
      L.and2(L.valid(y), L.valid(b), hy, L.and_r(L.valid(a), L.valid(b), hok))
    case False{} True{}:
      %Equal.sym(Bool, U32.is_eq(a, x), False{}, ea) : {L.hand_ok(G.U32s.replace.go(_, a, Con{b, Nil{}}, y, G.U32s.replace(Con{b, Nil{}}, x, y))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(b, x), True{}, eb) : {L.hand_ok(Con{a, G.U32s.replace.go(_, b, Nil{}, y, Nil{})}) == True{} : Bool}
      L.and2(L.valid(a), L.valid(y), L.and_l(L.valid(a), L.valid(b), hok), hy)
    case False{} False{}:
      %Equal.sym(Bool, U32.is_eq(a, x), False{}, ea) : {L.hand_ok(G.U32s.replace.go(_, a, Con{b, Nil{}}, y, G.U32s.replace(Con{b, Nil{}}, x, y))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(b, x), False{}, eb) : {L.hand_ok(Con{a, G.U32s.replace.go(_, b, Nil{}, y, Nil{})}) == True{} : Bool}
      hok

# Swapping a card for a deck card keeps a valid hand.
def L.replace_ok(+h: List<&2, U32>, +x: U32, +y: U32, +hok: {L.hand_ok(h) == True{} : Bool}, +hy: {L.valid(y) == True{} : Bool}) -> {L.hand_ok(G.U32s.replace(h, x, y)) == True{} : Bool}:
  match h:
    case Nil{}:
      Empty.absurd({L.hand_ok(Nil{}) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Nil{}}:
      Empty.absurd({L.hand_ok(G.U32s.replace(Con{a, Nil{}}, x, y)) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Con{b, Nil{}}}:
      L.replace_ok.go(a, b, x, y, U32.is_eq(a, x), {==}, U32.is_eq(b, x), {==}, hok, hy)
    case Con{a, Con{b, Con{d, rest}}}:
      Empty.absurd({L.hand_ok(G.U32s.replace(Con{a, Con{b, Con{d, rest}}}, x, y)) == True{} : Bool}, L.false_is_not_true(hok))

# ---- every legal move uses a card from the mover's hand

def L.add_card(+skip: Bool, +a: G.Action, +acc: List<&2, G.Action>, +m: G.Action, +h: {G.Actions.has(G.gen.add(skip, a, acc), m) == True{} : Bool}) -> {Bool.or(G.Action.same(a, m), G.Actions.has(acc, m)) == True{} : Bool}:
  match skip:
    case True{}:
      L.or_r(G.Action.same(a, m), G.Actions.has(acc, m), h)
    case False{}:
      h

def L.card_of_same.go(+card: U32, +from: G.Cell, +to: G.Cell, +mc: U32, +mf: G.Cell, +mt: G.Cell, +acc: List<&2, G.Action>, +b: Bool, +e: {G.Action.same(G.Action{card, from, to}, G.Action{mc, mf, mt}) == b : Bool}, +h: {Bool.or(G.Action.same(G.Action{card, from, to}, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}) -> {Bool.or(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match b:
    case True{}:
      +hs = L.and_l(Bool.and(U32.is_eq(card, mc), G.Cell.eq(from, mf)), G.Cell.eq(to, mt), e)
      %Equal.sym(Bool, U32.is_eq(card, mc), True{}, L.and_l(U32.is_eq(card, mc), G.Cell.eq(from, mf), hs)) : {Bool.or(_, G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}
      {==}
    case False{}:
      L.or_r(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt}), {%e : {Bool.or(_, G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}; h : {G.Actions.has(acc, G.Action{mc, mf, mt}) == True{} : Bool}})

def L.add_to_card(+t: Maybe<&2, G.Cell>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.add_to(t, card, from, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match t:
    case None{}:
      L.or_r(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Some{to}:
      +m = {G.Action{mc, mf, mt} : G.Action}
      +a = {G.Action{card, from, to} : G.Action}
      L.card_of_same.go(card, from, to, mc, mf, mt, acc, G.Action.same(a, m), {==}, L.add_card(G.Pieces.side_at(ps, to, side), a, acc, m, h))

def L.or_step.go(+x: Bool, +y: Bool, -z: Bool, +bx: Bool, +ex: {x == bx : Bool}, +hxy: {Bool.or(x, y) == True{} : Bool}, k: {y == True{} : Bool} -> {Bool.or(x, z) == True{} : Bool}) -> {Bool.or(x, z) == True{} : Bool}:
  match bx:
    case True{}:
      %Equal.sym(Bool, x, True{}, ex) : {Bool.or(_, z) == True{} : Bool}
      {==}
    case False{}:
      k({%ex : {Bool.or(_, y) == True{} : Bool}; hxy : {y == True{} : Bool}})

def L.steps_card(+sts: List<&2, G.Step>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.steps(sts, card, from, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match sts:
    case Nil{}:
      L.or_r(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Con{st, rest}:
      +t = G.Step.target(st, from, side)
      +acc2 = G.gen.add_to(t, card, from, side, ps, acc)
      +ih = L.steps_card(rest, card, from, side, ps, acc2, mc, mf, mt, h)
      L.or_step.go(U32.is_eq(card, mc), G.Actions.has(acc2, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt}), U32.is_eq(card, mc), {==}, ih, hy => L.add_to_card(t, card, from, side, ps, acc, mc, mf, mt, hy))

def L.one_card(+mine: Bool, +sts: List<&2, G.Step>, +card: U32, +q: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.pieces.one(mine, sts, card, q, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match mine:
    case True{}:
      L.steps_card(sts, card, q, side, ps, acc, mc, mf, mt, h)
    case False{}:
      L.or_r(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt}), h)

def L.pieces_card(+it: List<&2, G.Piece>, +card: U32, +sts: List<&2, G.Step>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.pieces(it, card, sts, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match it:
    case Nil{}:
      L.or_r(U32.is_eq(card, mc), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Con{G.Piece{s, t, q}, rest}:
      +acc2 = G.gen.pieces.one(G.Side.same(s, side), sts, card, q, side, ps, acc)
      +ih = L.pieces_card(rest, card, sts, side, ps, acc2, mc, mf, mt, h)
      L.or_step.go(U32.is_eq(card, mc), G.Actions.has(acc2, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt}), U32.is_eq(card, mc), {==}, ih, hy => L.one_card(G.Side.same(s, side), sts, card, q, side, ps, acc, mc, mf, mt, hy))

def L.cards_card.go(+c: U32, +rest: List<&2, U32>, +mc: U32, +acc: List<&2, G.Action>, +m: G.Action, -acc2: List<&2, G.Action>, +bc: Bool, +ec: {U32.is_eq(c, mc) == bc : Bool}, +br: Bool, +er: {G.U32s.has(rest, mc) == br : Bool}, +ih: {Bool.or(G.U32s.has(rest, mc), G.Actions.has(acc2, m)) == True{} : Bool}, k: {G.Actions.has(acc2, m) == True{} : Bool} -> {Bool.or(U32.is_eq(c, mc), G.Actions.has(acc, m)) == True{} : Bool}) -> {Bool.or(G.U32s.has(Con{c, rest}, mc), G.Actions.has(acc, m)) == True{} : Bool}:
  match bc br:
    case _ True{}:
      %Equal.sym(Bool, G.U32s.has(rest, mc), True{}, er) : {Bool.or(Bool.or(U32.is_eq(c, mc), _), G.Actions.has(acc, m)) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(U32.is_eq(c, mc), True{}), True{}, L.or_true_r(U32.is_eq(c, mc))) : {Bool.or(_, G.Actions.has(acc, m)) == True{} : Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, U32.is_eq(c, mc), True{}, ec) : {Bool.or(Bool.or(_, G.U32s.has(rest, mc)), G.Actions.has(acc, m)) == True{} : Bool}
      {==}
    case False{} False{}:
      +h2 = k({%er : {Bool.or(_, G.Actions.has(acc2, m)) == True{} : Bool}; ih : {G.Actions.has(acc2, m) == True{} : Bool}})
      +ha = {%ec : {Bool.or(_, G.Actions.has(acc, m)) == True{} : Bool}; h2 : {G.Actions.has(acc, m) == True{} : Bool}}
      L.or_r(G.U32s.has(Con{c, rest}, mc), G.Actions.has(acc, m), ha)

def L.cards_card(+hand: List<&2, U32>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.cards(hand, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(G.U32s.has(hand, mc), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match hand:
    case Nil{}:
      h
    case Con{c, rest}:
      +acc2 = G.gen.pieces(ps, c, G.card_steps(c), side, ps, acc)
      +ih = L.cards_card(rest, side, ps, acc2, mc, mf, mt, h)
      L.cards_card.go(c, rest, mc, acc, G.Action{mc, mf, mt}, acc2, U32.is_eq(c, mc), {==}, G.U32s.has(rest, mc), {==}, ih, hy => L.pieces_card(ps, c, G.card_steps(c), side, ps, acc, mc, mf, mt, hy))

# ---------------------------------------------------------------- the invariant: counting and goalkeepers

def L.count(+ps: List<&2, G.Piece>, +side: G.Side) -> Nat:
  G.Cells.len(L.own(ps, side))

def L.count_move.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +side: G.Side, +b: Bool, +e: {G.Side.same(s, side) == b : Bool}, +ih: {G.Cells.len(L.own(G.Pieces.move(rest, f, to), side)) == G.Cells.len(L.own(rest, side)) : Nat}) -> {G.Cells.len(L.own(G.Pieces.move(Con{G.Piece{s, t, q}, rest}, f, to), side)) == G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side)) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Side.same(s, side), True{}, e) : {G.Cells.len(L.pick(_, G.Cell.sel(G.Cell.eq(q, f), to, q) <> L.own(G.Pieces.move(rest, f, to), side), L.own(G.Pieces.move(rest, f, to), side))) == G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side))) : Nat}
      %ih : {1n+G.Cells.len(L.own(G.Pieces.move(rest, f, to), side)) == 1n+_ : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, G.Side.same(s, side), False{}, e) : {G.Cells.len(L.pick(_, G.Cell.sel(G.Cell.eq(q, f), to, q) <> L.own(G.Pieces.move(rest, f, to), side), L.own(G.Pieces.move(rest, f, to), side))) == G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side))) : Nat}
      ih

# Moving a piece keeps each side's count.
def L.count_move(+xs: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +side: G.Side) -> {G.Cells.len(L.own(G.Pieces.move(xs, f, to), side)) == G.Cells.len(L.own(xs, side)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.count_move.go(s, t, q, rest, f, to, side, G.Side.same(s, side), {==}, L.count_move(rest, f, to, side))

def L.count_capture.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side, +side: G.Side, +bh: Bool, +eh: {Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)) == bh : Bool}, +bs: Bool, +es: {G.Side.same(s, side) == bs : Bool}, +ih: {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture(rest, sq, e), side)), G.Cells.len(L.own(rest, side))) == True{} : Bool}) -> {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, sq, e), side)), G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side))) == True{} : Bool}:
  match bh bs:
    case True{} True{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), True{}, eh) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side)), G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side))) == True{} : Bool}
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture(rest, sq, e), side)), G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side)))) == True{} : Bool}
      L.le_succ(G.Cells.len(L.own(G.Pieces.capture(rest, sq, e), side)), G.Cells.len(L.own(rest, side)), ih)
    case True{} False{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), True{}, eh) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side)), G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side))) == True{} : Bool}
      %Equal.sym(Bool, G.Side.same(s, side), False{}, es) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture(rest, sq, e), side)), G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side)))) == True{} : Bool}
      ih
    case False{} True{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), False{}, eh) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side)), G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side))) == True{} : Bool}
      %Equal.sym(Bool, G.Side.same(s, side), True{}, es) : {Nat.is_le(G.Cells.len(L.pick(_, q <> L.own(G.Pieces.capture(rest, sq, e), side), L.own(G.Pieces.capture(rest, sq, e), side))), G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side)))) == True{} : Bool}
      ih
    case False{} False{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), False{}, eh) : {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side)), G.Cells.len(L.own(Con{G.Piece{s, t, q}, rest}, side))) == True{} : Bool}
      %Equal.sym(Bool, G.Side.same(s, side), False{}, es) : {Nat.is_le(G.Cells.len(L.pick(_, q <> L.own(G.Pieces.capture(rest, sq, e), side), L.own(G.Pieces.capture(rest, sq, e), side))), G.Cells.len(L.pick(_, q <> L.own(rest, side), L.own(rest, side)))) == True{} : Bool}
      ih

# Capturing never adds pieces to a side.
def L.count_capture(+xs: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side, +side: G.Side) -> {Nat.is_le(G.Cells.len(L.own(G.Pieces.capture(xs, sq, e), side)), G.Cells.len(L.own(xs, side))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.count_capture.go(s, t, q, rest, sq, e, side, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), {==}, G.Side.same(s, side), {==}, L.count_capture(rest, sq, e, side))

# After a move each side still has at most 7 pieces.
def L.count_after(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +f: G.Cell, +side: G.Side, +hc: {Nat.is_le(L.count(ps, side), 7n) == True{} : Bool}) -> {Nat.is_le(L.count(G.Pieces.move(G.Pieces.capture(ps, to, e), f, to), side), 7n) == True{} : Bool}:
  +cp = G.Pieces.capture(ps, to, e)
  %Equal.sym(Nat, G.Cells.len(L.own(G.Pieces.move(cp, f, to), side)), G.Cells.len(L.own(cp, side)), L.count_move(cp, f, to, side)) : {Nat.is_le(_, 7n) == True{} : Bool}
  L.le_trans(G.Cells.len(L.own(cp, side)), G.Cells.len(L.own(ps, side)), 7n, L.count_capture(ps, to, e, side), hc)

def L.keeper(+ps: List<&2, G.Piece>, +side: G.Side) -> Bool:
  Bool.not(G.Cell.none(G.Pieces.teacher_of(ps, side)))

def L.keeper_move.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +side: G.Side, +b: Bool, +e: {Bool.and(G.Side.same(s, side), t) == b : Bool}, +h: {L.keeper(Con{G.Piece{s, t, q}, rest}, side) == True{} : Bool}, ih: {L.keeper(rest, side) == True{} : Bool} -> {L.keeper(G.Pieces.move(rest, f, to), side) == True{} : Bool}) -> {L.keeper(G.Pieces.move(Con{G.Piece{s, t, q}, rest}, f, to), side) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, side), t), True{}, e) : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, G.Cell.sel(G.Cell.eq(q, f), to, q), G.Pieces.teacher_of(G.Pieces.move(rest, f, to), side)))) == True{} : Bool}
      {==}
    case False{}:
      +hr = {%e : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, side)))) == True{} : Bool}; h : {L.keeper(rest, side) == True{} : Bool}}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, side), t), False{}, e) : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, G.Cell.sel(G.Cell.eq(q, f), to, q), G.Pieces.teacher_of(G.Pieces.move(rest, f, to), side)))) == True{} : Bool}
      ih(hr)

# Moving keeps every goalkeeper on the board.
def L.keeper_move(+xs: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +side: G.Side, +h: {L.keeper(xs, side) == True{} : Bool}) -> {L.keeper(G.Pieces.move(xs, f, to), side) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{G.Piece{s, t, q}, rest}:
      L.keeper_move.go(s, t, q, rest, f, to, side, Bool.and(G.Side.same(s, side), t), {==}, h, h2 => L.keeper_move(rest, f, to, side, h2))

def L.keeper_enemy.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side, +bt: Bool, +et: {Bool.and(G.Side.same(s, e), t) == bt : Bool}, +bh: Bool, +eh: {Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)) == bh : Bool}, +hk: {L.keeper(Con{G.Piece{s, t, q}, rest}, e) == True{} : Bool}, +hn: {G.Cell.is(G.Pieces.teacher_of(Con{G.Piece{s, t, q}, rest}, e), sq) == False{} : Bool}, ih: {L.keeper(rest, e) == True{} : Bool} -> {G.Cell.is(G.Pieces.teacher_of(rest, e), sq) == False{} : Bool} -> {L.keeper(G.Pieces.capture(rest, sq, e), e) == True{} : Bool}) -> {L.keeper(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, sq, e), e) == True{} : Bool}:
  match bt bh:
    case True{} True{}:
      +hq = {%et : {G.Cell.is(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, e)), sq) == False{} : Bool}; hn : {G.Cell.eq(q, sq) == False{} : Bool}}
      +ss = L.and_l(G.Side.same(s, e), t, et)
      +hb = {%ss : {Bool.and(_, G.Cell.eq(q, sq)) == True{} : Bool}; eh : {G.Cell.eq(q, sq) == True{} : Bool}}
      Empty.absurd({L.keeper(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, sq, e), e) == True{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, G.Cell.eq(q, sq), False{}, Equal.sym(Bool, G.Cell.eq(q, sq), True{}, hb), hq)))
    case True{} False{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), False{}, eh) : {L.keeper(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), e) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), t), True{}, et) : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(G.Pieces.capture(rest, sq, e), e)))) == True{} : Bool}
      {==}
    case False{} True{}:
      +hr = {%et : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, e)))) == True{} : Bool}; hk : {L.keeper(rest, e) == True{} : Bool}}
      +nr = {%et : {G.Cell.is(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, e)), sq) == False{} : Bool}; hn : {G.Cell.is(G.Pieces.teacher_of(rest, e), sq) == False{} : Bool}}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), True{}, eh) : {L.keeper(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), e) == True{} : Bool}
      ih(hr, nr)
    case False{} False{}:
      +hr = {%et : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, e)))) == True{} : Bool}; hk : {L.keeper(rest, e) == True{} : Bool}}
      +nr = {%et : {G.Cell.is(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(rest, e)), sq) == False{} : Bool}; hn : {G.Cell.is(G.Pieces.teacher_of(rest, e), sq) == False{} : Bool}}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), False{}, eh) : {L.keeper(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), e) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), t), False{}, et) : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(G.Pieces.capture(rest, sq, e), e)))) == True{} : Bool}
      ih(hr, nr)

# A capture that did not land on the enemy goalkeeper leaves it on the board.
def L.keeper_enemy(+ps: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side, +hk: {L.keeper(ps, e) == True{} : Bool}, +hn: {G.Cell.is(G.Pieces.teacher_of(ps, e), sq) == False{} : Bool}) -> {L.keeper(G.Pieces.capture(ps, sq, e), e) == True{} : Bool}:
  match ps:
    case Nil{}:
      hk
    case Con{G.Piece{s, t, q}, rest}:
      L.keeper_enemy.go(s, t, q, rest, sq, e, Bool.and(G.Side.same(s, e), t), {==}, Bool.and(G.Side.same(s, e), G.Cell.eq(q, sq)), {==}, hk, hn, h2 => n2 => L.keeper_enemy(rest, sq, e, h2, n2))

def L.keeper_other.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +sq: G.Cell, +e: G.Side, +side: G.Side, +es: {Bool.and(G.Side.same(s, side), t) == False{} : Bool}, +b: Bool, +eb: {G.Cell.eq(q, sq) == b : Bool}, +ih: {L.keeper(G.Pieces.capture(rest, sq, e), side) == True{} : Bool}) -> {L.keeper(G.Pieces.capture.go(G.Cell.eq(q, sq), G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.Cell.eq(q, sq), True{}, eb) : {L.keeper(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side) == True{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, G.Cell.eq(q, sq), False{}, eb) : {L.keeper(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, sq, e)), side) == True{} : Bool}
      %Equal.sym(Bool, Bool.and(G.Side.same(s, side), t), False{}, es) : {Bool.not(G.Cell.none(G.Pieces.teacher_of.pick(_, q, G.Pieces.teacher_of(G.Pieces.capture(rest, sq, e), side)))) == True{} : Bool}
      ih

# Capturing `e`'s pieces never removes the other side's goalkeeper.
def L.keeper_other(+side: G.Side, +e: G.Side, +ps: List<&2, G.Piece>, +sq: G.Cell, +ne: {G.Side.same(side, e) == False{} : Bool}, +hk: {L.keeper(ps, side) == True{} : Bool}) -> {L.keeper(G.Pieces.capture(ps, sq, e), side) == True{} : Bool}:
  match side e ps:
    case G.Blue{} G.Blue{} _:
      Empty.absurd({L.keeper(G.Pieces.capture(ps, sq, G.Blue{}), G.Blue{}) == True{} : Bool}, L.true_is_not_false(ne))
    case G.Red{} G.Red{} _:
      Empty.absurd({L.keeper(G.Pieces.capture(ps, sq, G.Red{}), G.Red{}) == True{} : Bool}, L.true_is_not_false(ne))
    case G.Blue{} G.Red{} Nil{}:
      hk
    case G.Red{} G.Blue{} Nil{}:
      hk
    case G.Blue{} G.Red{} Con{G.Piece{G.Blue{}, True{}, q}, rest}:
      {==}
    case G.Red{} G.Blue{} Con{G.Piece{G.Red{}, True{}, q}, rest}:
      {==}
    case G.Blue{} G.Red{} Con{G.Piece{G.Blue{}, False{}, q}, rest}:
      L.keeper_other(G.Blue{}, G.Red{}, rest, sq, ne, hk)
    case G.Red{} G.Blue{} Con{G.Piece{G.Red{}, False{}, q}, rest}:
      L.keeper_other(G.Red{}, G.Blue{}, rest, sq, ne, hk)
    case G.Blue{} G.Red{} Con{G.Piece{G.Red{}, t, q}, rest}:
      L.keeper_other.go(G.Red{}, t, q, rest, sq, G.Red{}, G.Blue{}, {==}, G.Cell.eq(q, sq), {==}, L.keeper_other(G.Blue{}, G.Red{}, rest, sq, ne, hk))
    case G.Red{} G.Blue{} Con{G.Piece{G.Blue{}, t, q}, rest}:
      L.keeper_other.go(G.Blue{}, t, q, rest, sq, G.Blue{}, G.Red{}, {==}, G.Cell.eq(q, sq), {==}, L.keeper_other(G.Red{}, G.Blue{}, rest, sq, ne, hk))

# ---------------------------------------------------------------- the invariant of every reachable game

def L.inv(g: G.Game) -> Bool:
  match g:
    case G.Game{turn, +ps, b, r, tb, q, h, res}:
      Bool.and(L.hand_ok(b), Bool.and(L.hand_ok(r), Bool.and(L.valid(tb), Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))))))))

def L.inv_mk(+g: G.Game, +h1: {L.hand_ok(G.Game.hand(g, G.Blue{})) == True{} : Bool}, +h2: {L.hand_ok(G.Game.hand(g, G.Red{})) == True{} : Bool}, +h3: {L.valid(G.Game.table(g)) == True{} : Bool}, +h4: {Nat.is_le(L.count(G.Game.pieces(g), G.Blue{}), 7n) == True{} : Bool}, +h5: {Nat.is_le(L.count(G.Game.pieces(g), G.Red{}), 7n) == True{} : Bool}, +h6: {Bool.or(G.Outcome.is_over(G.Game.result(g)), Bool.and(L.keeper(G.Game.pieces(g), G.Blue{}), L.keeper(G.Game.pieces(g), G.Red{}))) == True{} : Bool}) -> {L.inv(g) == True{} : Bool}:
  match g:
    case G.Game{turn, ps, b, r, tb, q, h, res}:
      +k = Bool.or(G.Outcome.is_over(res), Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{})))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), k)
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      L.and2(L.hand_ok(b), Bool.and(L.hand_ok(r), c3), h1, L.and2(L.hand_ok(r), c3, h2, L.and2(L.valid(tb), c4, h3, L.and2(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, h4, L.and2(Nat.is_le(L.count(ps, G.Red{}), 7n), k, h5, h6)))))

def L.all_valid(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(L.valid(x), L.all_valid(t))

def L.nth_or_valid(+xs: List<&2, U32>, +n: Nat, +d: U32, +hs: {L.all_valid(xs) == True{} : Bool}, +hd: {L.valid(d) == True{} : Bool}) -> {L.valid(G.U32s.nth_or(xs, n, d)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      hd
    case Con{h, t} 0n:
      L.and_l(L.valid(h), L.all_valid(t), hs)
    case Con{h, t} 1n+p:
      L.nth_or_valid(t, p, d, L.and_r(L.valid(h), L.all_valid(t), hs), hd)

def L.remove_valid.go(+h: U32, +t: List<&2, U32>, +x: U32, +b: Bool, +e: {U32.is_eq(h, x) == b : Bool}, +hs: {Bool.and(L.valid(h), L.all_valid(t)) == True{} : Bool}, +ih: {L.all_valid(G.U32s.remove(t, x)) == True{} : Bool}) -> {L.all_valid(G.U32s.remove.go(U32.is_eq(h, x), h, t, G.U32s.remove(t, x))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(h, x), True{}, e) : {L.all_valid(G.U32s.remove.go(_, h, t, G.U32s.remove(t, x))) == True{} : Bool}
      L.and_r(L.valid(h), L.all_valid(t), hs)
    case False{}:
      %Equal.sym(Bool, U32.is_eq(h, x), False{}, e) : {L.all_valid(G.U32s.remove.go(_, h, t, G.U32s.remove(t, x))) == True{} : Bool}
      L.and2(L.valid(h), L.all_valid(G.U32s.remove(t, x)), L.and_l(L.valid(h), L.all_valid(t), hs), ih)

def L.remove_valid(+xs: List<&2, U32>, +x: U32, +hs: {L.all_valid(xs) == True{} : Bool}) -> {L.all_valid(G.U32s.remove(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.remove_valid.go(h, t, x, U32.is_eq(h, x), {==}, hs, L.remove_valid(t, x, L.and_r(L.valid(h), L.all_valid(t), hs)))

# Every card the draw picks is a deck card.
def L.drawn_valid(+n: Nat, +xs: List<&2, U32>, +r: U32, +hs: {L.all_valid(xs) == True{} : Bool}) -> {L.all_valid(G.draw_n(n, xs, r)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +c = G.draw_pick(xs, r)
      L.and2(L.valid(c), L.all_valid(G.draw_n(p, G.U32s.remove(xs, c), G.rng(r))), L.nth_or_valid(xs, U32.to_nat((r % U32.from_nat(G.U32s.len(xs)) : U32)), 0, hs, {==}), L.drawn_valid(p, G.U32s.remove(xs, c), G.rng(r), L.remove_valid(xs, c, hs)))

def L.deal_ok(d: G.Deal) -> Bool:
  match d:
    case G.Deal{b, r, t}:
      Bool.and(L.hand_ok(b), Bool.and(L.hand_ok(r), L.valid(t)))

def L.deal_list_ok(+l: List<&2, U32>, +h: {L.all_valid(l) == True{} : Bool}) -> {L.deal_ok(G.Deal.of_list(l)) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, rest}}}}}:
      +r4 = Bool.and(L.valid(e), L.all_valid(rest))
      +r3 = Bool.and(L.valid(d), r4)
      +r2 = Bool.and(L.valid(c), r3)
      +r1 = Bool.and(L.valid(b), r2)
      +va = L.and_l(L.valid(a), r1, h)
      +vb = L.and_l(L.valid(b), r2, L.and_r(L.valid(a), r1, h))
      +vc = L.and_l(L.valid(c), r3, L.and_r(L.valid(b), r2, L.and_r(L.valid(a), r1, h)))
      +vd = L.and_l(L.valid(d), r4, L.and_r(L.valid(c), r3, L.and_r(L.valid(b), r2, L.and_r(L.valid(a), r1, h))))
      +ve = L.and_l(L.valid(e), L.all_valid(rest), L.and_r(L.valid(d), r4, L.and_r(L.valid(c), r3, L.and_r(L.valid(b), r2, L.and_r(L.valid(a), r1, h)))))
      L.and2(Bool.and(L.valid(a), L.valid(b)), Bool.and(Bool.and(L.valid(c), L.valid(d)), L.valid(e)), L.and2(L.valid(a), L.valid(b), va, vb), L.and2(Bool.and(L.valid(c), L.valid(d)), L.valid(e), L.and2(L.valid(c), L.valid(d), vc, vd), ve))

def L.keepers_start(+s: G.Side) -> {Bool.and(L.keeper(G.Pieces.start(), G.Blue{}), L.keeper(G.Pieces.start(), G.Red{})) == True{} : Bool}:
  {==}

def L.inv_dealt(+starter: G.Side, +d: G.Deal, +hd: {L.deal_ok(d) == True{} : Bool}) -> {L.inv(G.start_dealt(starter, d)) == True{} : Bool}:
  match d:
    case G.Deal{b, r, t}:
      +g = G.start_dealt(starter, G.Deal{b, r, t})
      +rest = Bool.and(L.hand_ok(r), L.valid(t))
      L.inv_mk(g, L.and_l(L.hand_ok(b), rest, hd), L.and_l(L.hand_ok(r), L.valid(t), L.and_r(L.hand_ok(b), rest, hd)), L.and_r(L.hand_ok(r), L.valid(t), L.and_r(L.hand_ok(b), rest, hd)), {==}, {==}, {==})

# The first position satisfies the invariant.
# ---------------------------------------------------------------- the draw: turning keeps the deck

def L.d_or_l(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def L.d_not_in(-x: Bool, -y: Bool, +b: Bool, +eb: {x == b : Bool}, k: {x == True{} : Bool} -> {y == True{} : Bool}, +hy: {y == False{} : Bool}) -> {x == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({x == False{} : Bool}, L.false_is_not_true(Equal.trans(Bool, False{}, y, True{}, Equal.sym(Bool, y, False{}, hy), k(eb))))

def L.or_false_id(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def L.or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def L.or_comm(+a: Bool, +b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def L.has_snoc(+t: List<&2, U32>, +h: U32, +x: U32) -> {G.U32s.has(G.U32s.append(t, [h]), x) == Bool.or(G.U32s.has(t, x), U32.is_eq(h, x)) : Bool}:
  match t:
    case Nil{}:
      L.or_false_id(U32.is_eq(h, x))
    case Con{y, r}:
      %Equal.sym(Bool, G.U32s.has(G.U32s.append(r, [h]), x), Bool.or(G.U32s.has(r, x), U32.is_eq(h, x)), L.has_snoc(r, h, x)) : {Bool.or(U32.is_eq(y, x), _) == Bool.or(Bool.or(U32.is_eq(y, x), G.U32s.has(r, x)), U32.is_eq(h, x)) : Bool}
      L.or_assoc(U32.is_eq(y, x), G.U32s.has(r, x), U32.is_eq(h, x))

def L.rot1_has(+xs: List<&2, U32>, +x: U32) -> {G.U32s.has(G.U32s.rot1(xs), x) == G.U32s.has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, G.U32s.has(G.U32s.append(t, [h]), x), Bool.or(G.U32s.has(t, x), U32.is_eq(h, x)), L.has_snoc(t, h, x)) : {_ == Bool.or(U32.is_eq(h, x), G.U32s.has(t, x)) : Bool}
      L.or_comm(G.U32s.has(t, x), U32.is_eq(h, x))

# Turning the deck keeps every card.
def L.rot_has(+k: Nat, +xs: List<&2, U32>, +x: U32) -> {G.U32s.has(G.U32s.rotate(k, xs), x) == G.U32s.has(xs, x) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Bool, G.U32s.has(G.U32s.rotate(p, G.U32s.rot1(xs)), x), G.U32s.has(G.U32s.rot1(xs), x), G.U32s.has(xs, x), L.rot_has(p, G.U32s.rot1(xs), x), L.rot1_has(xs, x))

def L.len_snoc(+t: List<&2, U32>, +h: U32) -> {G.U32s.len(G.U32s.append(t, [h])) == 1n+G.U32s.len(t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Con{y, r}:
      %Equal.sym(Nat, G.U32s.len(G.U32s.append(r, [h])), 1n+G.U32s.len(r), L.len_snoc(r, h)) : {1n+_ == 1n+1n+G.U32s.len(r) : Nat}
      {==}

def L.rot1_len(+xs: List<&2, U32>) -> {G.U32s.len(G.U32s.rot1(xs)) == G.U32s.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.len_snoc(t, h)

def L.rot_len(+k: Nat, +xs: List<&2, U32>) -> {G.U32s.len(G.U32s.rotate(k, xs)) == G.U32s.len(xs) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, G.U32s.len(G.U32s.rotate(p, G.U32s.rot1(xs))), G.U32s.len(G.U32s.rot1(xs)), G.U32s.len(xs), L.rot_len(p, G.U32s.rot1(xs)), L.rot1_len(xs))

def L.u32_eq_sym.go(+a: U32, +b: U32, +x: Bool, +ex: {U32.is_eq(a, b) == x : Bool}, +y: Bool, +ey: {U32.is_eq(b, a) == y : Bool}) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  match x y:
    case True{} _:
      %L.u32_eq_true(a, b, ex) : {U32.is_eq(a, _) == U32.is_eq(_, a) : Bool}
      {==}
    case False{} True{}:
      %L.u32_eq_true(b, a, ey) : {U32.is_eq(_, b) == U32.is_eq(b, _) : Bool}
      {==}
    case False{} False{}:
      Equal.trans(Bool, U32.is_eq(a, b), False{}, U32.is_eq(b, a), ex, Equal.sym(Bool, U32.is_eq(b, a), False{}, ey))

def L.u32_eq_sym(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  L.u32_eq_sym.go(a, b, U32.is_eq(a, b), {==}, U32.is_eq(b, a), {==})

def L.bool4(+a: Bool, +b: Bool, +c: Bool, +d: Bool) -> {Bool.and(Bool.not(Bool.or(a, b)), Bool.and(Bool.not(c), d)) == Bool.and(Bool.not(Bool.or(b, c)), Bool.and(Bool.not(a), d)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def L.dist_snoc(+t: List<&2, U32>, +h: U32) -> {G.U32s.distinct(G.U32s.append(t, [h])) == Bool.and(Bool.not(G.U32s.has(t, h)), G.U32s.distinct(t)) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{y, r}:
      %Equal.sym(Bool, G.U32s.has(G.U32s.append(r, [h]), y), Bool.or(G.U32s.has(r, y), U32.is_eq(h, y)), L.has_snoc(r, h, y)) : {Bool.and(Bool.not(_), G.U32s.distinct(G.U32s.append(r, [h]))) == Bool.and(Bool.not(Bool.or(U32.is_eq(y, h), G.U32s.has(r, h))), Bool.and(Bool.not(G.U32s.has(r, y)), G.U32s.distinct(r))) : Bool}
      %Equal.sym(Bool, G.U32s.distinct(G.U32s.append(r, [h])), Bool.and(Bool.not(G.U32s.has(r, h)), G.U32s.distinct(r)), L.dist_snoc(r, h)) : {Bool.and(Bool.not(Bool.or(G.U32s.has(r, y), U32.is_eq(h, y))), _) == Bool.and(Bool.not(Bool.or(U32.is_eq(y, h), G.U32s.has(r, h))), Bool.and(Bool.not(G.U32s.has(r, y)), G.U32s.distinct(r))) : Bool}
      %L.u32_eq_sym(y, h) : {Bool.and(Bool.not(Bool.or(G.U32s.has(r, y), _)), Bool.and(Bool.not(G.U32s.has(r, h)), G.U32s.distinct(r))) == Bool.and(Bool.not(Bool.or(U32.is_eq(y, h), G.U32s.has(r, h))), Bool.and(Bool.not(G.U32s.has(r, y)), G.U32s.distinct(r))) : Bool}
      L.bool4(G.U32s.has(r, y), U32.is_eq(y, h), G.U32s.has(r, h), G.U32s.distinct(r))

def L.rot1_dist(+xs: List<&2, U32>) -> {G.U32s.distinct(G.U32s.rot1(xs)) == G.U32s.distinct(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.dist_snoc(t, h)

def L.rot_dist(+k: Nat, +xs: List<&2, U32>) -> {G.U32s.distinct(G.U32s.rotate(k, xs)) == G.U32s.distinct(xs) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(p, G.U32s.rot1(xs))), G.U32s.distinct(G.U32s.rot1(xs)), G.U32s.distinct(xs), L.rot_dist(p, G.U32s.rot1(xs)), L.rot1_dist(xs))

def L.and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def L.and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def L.and_true_id(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def L.in_snoc(+t: List<&2, U32>, +h: U32, +ys: List<&2, U32>) -> {G.U32s.all_in(G.U32s.append(t, [h]), ys) == Bool.and(G.U32s.all_in(t, ys), G.U32s.has(ys, h)) : Bool}:
  match t:
    case Nil{}:
      L.and_true_id(G.U32s.has(ys, h))
    case Con{y, r}:
      %Equal.sym(Bool, G.U32s.all_in(G.U32s.append(r, [h]), ys), Bool.and(G.U32s.all_in(r, ys), G.U32s.has(ys, h)), L.in_snoc(r, h, ys)) : {Bool.and(G.U32s.has(ys, y), _) == Bool.and(Bool.and(G.U32s.has(ys, y), G.U32s.all_in(r, ys)), G.U32s.has(ys, h)) : Bool}
      L.and_assoc(G.U32s.has(ys, y), G.U32s.all_in(r, ys), G.U32s.has(ys, h))

def L.rot1_in(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {G.U32s.all_in(G.U32s.rot1(xs), ys) == G.U32s.all_in(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, G.U32s.all_in(G.U32s.append(t, [h]), ys), Bool.and(G.U32s.all_in(t, ys), G.U32s.has(ys, h)), L.in_snoc(t, h, ys)) : {_ == Bool.and(G.U32s.has(ys, h), G.U32s.all_in(t, ys)) : Bool}
      L.and_comm(G.U32s.all_in(t, ys), G.U32s.has(ys, h))

def L.rot_in(+k: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>) -> {G.U32s.all_in(G.U32s.rotate(k, xs), ys) == G.U32s.all_in(xs, ys) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Bool, G.U32s.all_in(G.U32s.rotate(p, G.U32s.rot1(xs)), ys), G.U32s.all_in(G.U32s.rot1(xs), ys), G.U32s.all_in(xs, ys), L.rot_in(p, G.U32s.rot1(xs), ys), L.rot1_in(xs, ys))

# ---- the drawn cards: as many as asked, all different, all from the deck

def L.draw_len(+n: Nat, +rot: List<&2, U32>, +bs: List<&2, Nat>, +rs: List<&2, Nat>, +hl: {Nat.is_le(n, G.U32s.len(rot)) == True{} : Bool}) -> {G.U32s.len(G.Draw.go(n, rot, bs, rs)) == n : Nat}:
  match n rot:
    case 0n Nil{}:
      {==}
    case 0n Con{c, rest}:
      {==}
    case 1n+p Nil{}:
      Empty.absurd({0n == 1n+p : Nat}, L.false_is_not_true(hl))
    case 1n+p Con{c, rest}:
      +hl2 = {%Equal.sym(Nat, G.U32s.len(G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest)), G.U32s.len(rest), L.rot_len(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest)) : {Nat.is_le(p, _) == True{} : Bool}; hl : {Nat.is_le(p, G.U32s.len(G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest))) == True{} : Bool}}
      %Equal.sym(Nat, G.U32s.len(G.Draw.go(p, G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest), G.Nats.tail(bs), G.Nats.tail(rs))), p, L.draw_len(p, G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest), G.Nats.tail(bs), G.Nats.tail(rs), hl2)) : {1n+_ == 1n+p : Nat}
      {==}

def L.draw_in.go(+c: U32, +rest: List<&2, U32>, +x: U32, -d2: List<&2, U32>, +b: Bool, +eb: {U32.is_eq(c, x) == b : Bool}, +h: {Bool.or(U32.is_eq(c, x), G.U32s.has(d2, x)) == True{} : Bool}, ih: {G.U32s.has(d2, x) == True{} : Bool} -> {G.U32s.has(rest, x) == True{} : Bool}) -> {G.U32s.has(Con{c, rest}, x) == True{} : Bool}:
  match b:
    case True{}:
      L.d_or_l(U32.is_eq(c, x), G.U32s.has(rest, x), eb)
    case False{}:
      L.or_r(U32.is_eq(c, x), G.U32s.has(rest, x), ih({%eb : {Bool.or(_, G.U32s.has(d2, x)) == True{} : Bool}; h : {G.U32s.has(d2, x) == True{} : Bool}}))

def L.draw_in(+n: Nat, +rot: List<&2, U32>, +bs: List<&2, Nat>, +rs: List<&2, Nat>, +x: U32, +h: {G.U32s.has(G.Draw.go(n, rot, bs, rs), x) == True{} : Bool}) -> {G.U32s.has(rot, x) == True{} : Bool}:
  match n rot:
    case 0n Nil{}:
      h
    case 0n Con{c, rest}:
      Empty.absurd({G.U32s.has(Con{c, rest}, x) == True{} : Bool}, L.false_is_not_true(h))
    case 1n+p Nil{}:
      h
    case 1n+p Con{c, rest}:
      +r2 = G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest)
      L.draw_in.go(c, rest, x, G.Draw.go(p, r2, G.Nats.tail(bs), G.Nats.tail(rs)), U32.is_eq(c, x), {==}, h, h2 => Equal.trans(Bool, G.U32s.has(rest, x), G.U32s.has(r2, x), True{}, Equal.sym(Bool, G.U32s.has(r2, x), G.U32s.has(rest, x), L.rot_has(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest, x)), L.draw_in(p, r2, G.Nats.tail(bs), G.Nats.tail(rs), x, h2)))

def L.draw_dist(+n: Nat, +rot: List<&2, U32>, +bs: List<&2, Nat>, +rs: List<&2, Nat>, +hd: {G.U32s.distinct(rot) == True{} : Bool}) -> {G.U32s.distinct(G.Draw.go(n, rot, bs, rs)) == True{} : Bool}:
  match n rot:
    case 0n Nil{}:
      {==}
    case 0n Con{c, rest}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{c, rest}:
      +r2 = G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest)
      +d2 = G.Draw.go(p, r2, G.Nats.tail(bs), G.Nats.tail(rs))
      +nr = L.not_true(G.U32s.has(rest, c), L.and_l(Bool.not(G.U32s.has(rest, c)), G.U32s.distinct(rest), hd))
      +nin = L.d_not_in(G.U32s.has(d2, c), G.U32s.has(rest, c), G.U32s.has(d2, c), {==}, h2 => Equal.trans(Bool, G.U32s.has(rest, c), G.U32s.has(r2, c), True{}, Equal.sym(Bool, G.U32s.has(r2, c), G.U32s.has(rest, c), L.rot_has(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest, c)), L.draw_in(p, r2, G.Nats.tail(bs), G.Nats.tail(rs), c, h2)), nr)
      +dr = Equal.trans(Bool, G.U32s.distinct(r2), G.U32s.distinct(rest), True{}, L.rot_dist(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest), L.and_r(Bool.not(G.U32s.has(rest, c)), G.U32s.distinct(rest), hd))
      L.and2(Bool.not(G.U32s.has(d2, c)), G.U32s.distinct(d2), L.not_false(G.U32s.has(d2, c), nin), L.draw_dist(p, r2, G.Nats.tail(bs), G.Nats.tail(rs), dr))

def L.draw_ids(+n: Nat, +rot: List<&2, U32>, +bs: List<&2, Nat>, +rs: List<&2, Nat>, +ys: List<&2, U32>, +ha: {G.U32s.all_in(rot, ys) == True{} : Bool}) -> {G.U32s.all_in(G.Draw.go(n, rot, bs, rs), ys) == True{} : Bool}:
  match n rot:
    case 0n Nil{}:
      {==}
    case 0n Con{c, rest}:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{c, rest}:
      +r2 = G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest)
      +ar = Equal.trans(Bool, G.U32s.all_in(r2, ys), G.U32s.all_in(rest, ys), True{}, L.rot_in(G.Draw.k(G.Nats.tail(bs), G.Nats.tail(rs)), rest, ys), L.and_r(G.U32s.has(ys, c), G.U32s.all_in(rest, ys), ha))
      L.and2(G.U32s.has(ys, c), G.U32s.all_in(G.Draw.go(p, r2, G.Nats.tail(bs), G.Nats.tail(rs)), ys), L.and_l(G.U32s.has(ys, c), G.U32s.all_in(rest, ys), ha), L.draw_ids(p, r2, G.Nats.tail(bs), G.Nats.tail(rs), ys, ar))

def L.nat_eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      L.nat_eq_refl(p)

def L.nat_ne(+a: Nat, +b: Nat, +e: {a == b : Nat}, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> Empty:
  +c = Equal.cong(Nat, Bool, x => Nat.is_eq(a, x), a, b, e)
  L.true_is_not_false(Equal.trans(Bool, True{}, Nat.is_eq(a, b), False{}, Equal.trans(Bool, True{}, Nat.is_eq(a, a), Nat.is_eq(a, b), Equal.sym(Bool, Nat.is_eq(a, a), True{}, L.nat_eq_refl(a)), c), ne))

def L.of_list_valid(+l: List<&2, U32>, +hl: {G.U32s.len(l) == 5n : Nat}, +hd: {G.U32s.distinct(l) == True{} : Bool}, +ha: {G.U32s.all_in(l, G.Cards.ids(G.deck())) == True{} : Bool}) -> {G.Deal.is_valid(G.Deal.of_list(l)) == True{} : Bool}:
  match l:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      L.and2(G.U32s.distinct(Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}), G.U32s.all_in(Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}, G.Cards.ids(G.deck())), hd, ha)
    case Nil{}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Nil{})) == True{} : Bool}, L.nat_ne(G.U32s.len(Nil{}), 5n, hl, {==}))
    case Con{a, Nil{}}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Con{a, Nil{}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Nil{}}), 5n, hl, {==}))
    case Con{a, Con{b, Nil{}}}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Con{a, Con{b, Nil{}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Nil{}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Nil{}}}}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Con{a, Con{b, Con{c, Nil{}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Nil{}}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Con{a, Con{b, Con{c, Con{d, Nil{}}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Con{d, Nil{}}}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}}:
      Empty.absurd({G.Deal.is_valid(G.Deal.of_list(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}}), 5n, hl, {==}))

def L.deal_ok_of(+l: List<&2, U32>, +hl: {G.U32s.len(l) == 5n : Nat}, +ha: {G.U32s.all_in(l, G.Cards.ids(G.deck())) == True{} : Bool}) -> {L.deal_ok(G.Deal.of_list(l)) == True{} : Bool}:
  match l:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      +r4 = Bool.and(G.U32s.has(G.Cards.ids(G.deck()), e), True{})
      +r3 = Bool.and(G.U32s.has(G.Cards.ids(G.deck()), d), r4)
      +r2 = Bool.and(G.U32s.has(G.Cards.ids(G.deck()), c), r3)
      +r1 = Bool.and(G.U32s.has(G.Cards.ids(G.deck()), b), r2)
      +va = L.and_l(G.U32s.has(G.Cards.ids(G.deck()), a), r1, ha)
      +h1 = L.and_r(G.U32s.has(G.Cards.ids(G.deck()), a), r1, ha)
      +vb = L.and_l(G.U32s.has(G.Cards.ids(G.deck()), b), r2, h1)
      +h2 = L.and_r(G.U32s.has(G.Cards.ids(G.deck()), b), r2, h1)
      +vc = L.and_l(G.U32s.has(G.Cards.ids(G.deck()), c), r3, h2)
      +h3 = L.and_r(G.U32s.has(G.Cards.ids(G.deck()), c), r3, h2)
      +vd = L.and_l(G.U32s.has(G.Cards.ids(G.deck()), d), r4, h3)
      +ve = L.and_l(G.U32s.has(G.Cards.ids(G.deck()), e), True{}, L.and_r(G.U32s.has(G.Cards.ids(G.deck()), d), r4, h3))
      L.and2(Bool.and(G.U32s.has(G.Cards.ids(G.deck()), a), G.U32s.has(G.Cards.ids(G.deck()), b)), Bool.and(Bool.and(G.U32s.has(G.Cards.ids(G.deck()), c), G.U32s.has(G.Cards.ids(G.deck()), d)), G.U32s.has(G.Cards.ids(G.deck()), e)), L.and2(G.U32s.has(G.Cards.ids(G.deck()), a), G.U32s.has(G.Cards.ids(G.deck()), b), va, vb), L.and2(Bool.and(G.U32s.has(G.Cards.ids(G.deck()), c), G.U32s.has(G.Cards.ids(G.deck()), d)), G.U32s.has(G.Cards.ids(G.deck()), e), L.and2(G.U32s.has(G.Cards.ids(G.deck()), c), G.U32s.has(G.Cards.ids(G.deck()), d), vc, vd), ve))
    case Nil{}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Nil{})) == True{} : Bool}, L.nat_ne(G.U32s.len(Nil{}), 5n, hl, {==}))
    case Con{a, Nil{}}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Con{a, Nil{}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Nil{}}), 5n, hl, {==}))
    case Con{a, Con{b, Nil{}}}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Con{a, Con{b, Nil{}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Nil{}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Nil{}}}}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Con{a, Con{b, Con{c, Nil{}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Nil{}}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Con{a, Con{b, Con{c, Con{d, Nil{}}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Con{d, Nil{}}}}}), 5n, hl, {==}))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}}:
      Empty.absurd({L.deal_ok(G.Deal.of_list(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}})) == True{} : Bool}, L.nat_ne(G.U32s.len(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, r}}}}}}), 5n, hl, {==}))

def L.deal_parts(+bs: List<&2, Nat>, +rs: List<&2, Nat>) -> {G.U32s.len(G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs)) == 5n : Nat}:
  +hl = {%Equal.sym(Nat, G.U32s.len(G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck()))), G.U32s.len(G.Cards.ids(G.deck())), L.rot_len(G.Draw.k(bs, rs), G.Cards.ids(G.deck()))) : {Nat.is_le(5n, _) == True{} : Bool}; {==} : {Nat.is_le(5n, G.U32s.len(G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())))) == True{} : Bool}}
  L.draw_len(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs, hl)

def L.deal_ids(+bs: List<&2, Nat>, +rs: List<&2, Nat>) -> {G.U32s.all_in(G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs), G.Cards.ids(G.deck())) == True{} : Bool}:
  L.draw_ids(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs, G.Cards.ids(G.deck()), Equal.trans(Bool, G.U32s.all_in(G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), G.Cards.ids(G.deck())), G.U32s.all_in(G.Cards.ids(G.deck()), G.Cards.ids(G.deck())), True{}, L.rot_in(G.Draw.k(bs, rs), G.Cards.ids(G.deck()), G.Cards.ids(G.deck())), {==}))

def L.deal_dist(+bs: List<&2, Nat>, +rs: List<&2, Nat>) -> {G.U32s.distinct(G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs)) == True{} : Bool}:
  L.draw_dist(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs, Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck()))), G.U32s.distinct(G.Cards.ids(G.deck())), True{}, L.rot_dist(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), {==}))

# Every deal is valid: 2 + 2 + 1 different deck cards.
def L.deal_valid(+blue: G.Secret, +red: G.Secret) -> {G.Deal.is_valid(G.deal_from(blue, red)) == True{} : Bool}:
  match blue red:
    case G.Secret{bc, bs} G.Secret{rc, rs}:
      L.of_list_valid(G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs), L.deal_parts(bs, rs), L.deal_dist(bs, rs), L.deal_ids(bs, rs))

def L.inv_start(+setup: G.Setup) -> {L.inv(G.start(setup)) == True{} : Bool}:
  match setup:
    case G.Setup{G.Secret{bc, bs}, G.Secret{rc, rs}}:
      +dl = G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs)
      L.inv_dealt(G.Setup.starter(G.Setup{G.Secret{bc, bs}, G.Secret{rc, rs}}), G.Deal.of_list(dl), L.deal_ok_of(dl, L.deal_parts(bs, rs), L.deal_ids(bs, rs)))

def L.or_false_drop(+a: Bool, +h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h


def L.inv_apply_Blue.go(+ps: List<&2, G.Piece>, +b: List<&2, U32>, +r: List<&2, U32>, +tb: U32, +q: Nat, +hst: List<&2, U32>, +res: G.Outcome, +c: U32, +f: G.Cell, +to: G.Cell, +bo: Bool, +eo: {G.Outcome.is_over(res) == bo : Bool}, +bw: Bool, +ew: {G.won(ps, G.Red{}, to) == bw : Bool}, +hi: {L.inv(G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}) == True{} : Bool}, +legal: {G.is_legal(G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to}) == True{} : Bool}) -> {L.inv(G.apply(G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to})) == True{} : Bool}:
  match bo bw:
    case True{} _:
      Empty.absurd({L.inv(G.apply(G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to})) == True{} : Bool}, L.false_is_not_true({%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {False{} == True{} : Bool}}))
    case False{} True{}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +vtb = L.and_l(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi)))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%eo : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      +kB = L.and_l(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +kR = L.and_r(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {G.Actions.has(G.gen.cards(b, G.Blue{}, ps, Nil{}), G.Action{c, f, to}) == True{} : Bool}}
      +vc = L.hand_has(b, c, hok_b, L.or_false_drop(G.U32s.has(b, c), L.cards_card(b, G.Blue{}, ps, Nil{}, c, f, to, lg)))
      +p2 = G.Pieces.move(G.Pieces.capture(ps, to, G.Red{}), f, to)
      +g2 = G.apply.go(True{}, G.Blue{}, ps, b, r, tb, q, hst, c, f, to)
      %Equal.sym(Bool, G.won(ps, G.Red{}, to), True{}, ew) : {L.inv(G.apply.go(_, G.Blue{}, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      L.inv_mk(g2, L.replace_ok(b, c, tb, hok_b, vtb), hok_r, vc, L.count_after(ps, to, G.Red{}, f, G.Blue{}, hcB), L.count_after(ps, to, G.Red{}, f, G.Red{}, hcR), {==})
    case False{} False{}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +vtb = L.and_l(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi)))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%eo : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      +kB = L.and_l(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +kR = L.and_r(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {G.Actions.has(G.gen.cards(b, G.Blue{}, ps, Nil{}), G.Action{c, f, to}) == True{} : Bool}}
      +vc = L.hand_has(b, c, hok_b, L.or_false_drop(G.U32s.has(b, c), L.cards_card(b, G.Blue{}, ps, Nil{}, c, f, to, lg)))
      +p2 = G.Pieces.move(G.Pieces.capture(ps, to, G.Red{}), f, to)
      +g2 = G.apply.go(False{}, G.Blue{}, ps, b, r, tb, q, hst, c, f, to)
      +hn = L.or_false_l(G.Cell.is(G.Pieces.teacher_of(ps, G.Red{}), to), G.Cell.eq(to, G.Side.home(G.Red{})), ew)
      +kE2 = L.keeper_move(G.Pieces.capture(ps, to, G.Red{}), f, to, G.Red{}, L.keeper_enemy(ps, to, G.Red{}, kR, hn))
      +kT2 = L.keeper_move(G.Pieces.capture(ps, to, G.Red{}), f, to, G.Blue{}, L.keeper_other(G.Blue{}, G.Red{}, ps, to, {==}, kB))
      +h6 = L.or_r(G.Outcome.is_over(G.Game.result(g2)), Bool.and(L.keeper(p2, G.Blue{}), L.keeper(p2, G.Red{})), L.and2(L.keeper(p2, G.Blue{}), L.keeper(p2, G.Red{}), kT2, kE2))
      %Equal.sym(Bool, G.won(ps, G.Red{}, to), False{}, ew) : {L.inv(G.apply.go(_, G.Blue{}, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      L.inv_mk(g2, L.replace_ok(b, c, tb, hok_b, vtb), hok_r, vc, L.count_after(ps, to, G.Red{}, f, G.Blue{}, hcB), L.count_after(ps, to, G.Red{}, f, G.Red{}, hcR), h6)

def L.inv_apply_Red.go(+ps: List<&2, G.Piece>, +b: List<&2, U32>, +r: List<&2, U32>, +tb: U32, +q: Nat, +hst: List<&2, U32>, +res: G.Outcome, +c: U32, +f: G.Cell, +to: G.Cell, +bo: Bool, +eo: {G.Outcome.is_over(res) == bo : Bool}, +bw: Bool, +ew: {G.won(ps, G.Blue{}, to) == bw : Bool}, +hi: {L.inv(G.Game{G.Red{}, ps, b, r, tb, q, hst, res}) == True{} : Bool}, +legal: {G.is_legal(G.Game{G.Red{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to}) == True{} : Bool}) -> {L.inv(G.apply(G.Game{G.Red{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to})) == True{} : Bool}:
  match bo bw:
    case True{} _:
      Empty.absurd({L.inv(G.apply(G.Game{G.Red{}, ps, b, r, tb, q, hst, res}, G.Action{c, f, to})) == True{} : Bool}, L.false_is_not_true({%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Red{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {False{} == True{} : Bool}}))
    case False{} True{}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +vtb = L.and_l(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi)))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%eo : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      +kB = L.and_l(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +kR = L.and_r(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Red{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {G.Actions.has(G.gen.cards(r, G.Red{}, ps, Nil{}), G.Action{c, f, to}) == True{} : Bool}}
      +vc = L.hand_has(r, c, hok_r, L.or_false_drop(G.U32s.has(r, c), L.cards_card(r, G.Red{}, ps, Nil{}, c, f, to, lg)))
      +p2 = G.Pieces.move(G.Pieces.capture(ps, to, G.Blue{}), f, to)
      +g2 = G.apply.go(True{}, G.Red{}, ps, b, r, tb, q, hst, c, f, to)
      %Equal.sym(Bool, G.won(ps, G.Blue{}, to), True{}, ew) : {L.inv(G.apply.go(_, G.Red{}, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      L.inv_mk(g2, hok_b, L.replace_ok(r, c, tb, hok_r, vtb), vc, L.count_after(ps, to, G.Blue{}, f, G.Blue{}, hcB), L.count_after(ps, to, G.Blue{}, f, G.Red{}, hcR), {==})
    case False{} False{}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +vtb = L.and_l(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi)))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%eo : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      +kB = L.and_l(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +kR = L.and_r(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk)
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, G.Game{G.Red{}, ps, b, r, tb, q, hst, res}), G.Action{c, f, to}) == True{} : Bool}; legal : {G.Actions.has(G.gen.cards(r, G.Red{}, ps, Nil{}), G.Action{c, f, to}) == True{} : Bool}}
      +vc = L.hand_has(r, c, hok_r, L.or_false_drop(G.U32s.has(r, c), L.cards_card(r, G.Red{}, ps, Nil{}, c, f, to, lg)))
      +p2 = G.Pieces.move(G.Pieces.capture(ps, to, G.Blue{}), f, to)
      +g2 = G.apply.go(False{}, G.Red{}, ps, b, r, tb, q, hst, c, f, to)
      +hn = L.or_false_l(G.Cell.is(G.Pieces.teacher_of(ps, G.Blue{}), to), G.Cell.eq(to, G.Side.home(G.Blue{})), ew)
      +kE2 = L.keeper_move(G.Pieces.capture(ps, to, G.Blue{}), f, to, G.Blue{}, L.keeper_enemy(ps, to, G.Blue{}, kB, hn))
      +kT2 = L.keeper_move(G.Pieces.capture(ps, to, G.Blue{}), f, to, G.Red{}, L.keeper_other(G.Red{}, G.Blue{}, ps, to, {==}, kR))
      +h6 = L.or_r(G.Outcome.is_over(G.Game.result(g2)), Bool.and(L.keeper(p2, G.Blue{}), L.keeper(p2, G.Red{})), L.and2(L.keeper(p2, G.Blue{}), L.keeper(p2, G.Red{}), kE2, kT2))
      %Equal.sym(Bool, G.won(ps, G.Blue{}, to), False{}, ew) : {L.inv(G.apply.go(_, G.Red{}, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      L.inv_mk(g2, hok_b, L.replace_ok(r, c, tb, hok_r, vtb), vc, L.count_after(ps, to, G.Blue{}, f, G.Blue{}, hcB), L.count_after(ps, to, G.Blue{}, f, G.Red{}, hcR), h6)

def L.inv_apply(+g: G.Game, +m: G.Action, +hi: {L.inv(g) == True{} : Bool}, +legal: {G.is_legal(g, m) == True{} : Bool}) -> {L.inv(G.apply(g, m)) == True{} : Bool}:
  match g m:
    case G.Game{G.Blue{}, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      L.inv_apply_Blue.go(ps, b, r, tb, q, hst, res, c, f, to, G.Outcome.is_over(res), {==}, G.won(ps, G.Red{}, to), {==}, hi, legal)
    case G.Game{G.Red{}, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      L.inv_apply_Red.go(ps, b, r, tb, q, hst, res, c, f, to, G.Outcome.is_over(res), {==}, G.won(ps, G.Blue{}, to), {==}, hi, legal)

def L.inv_play.go(+g: G.Game, +m: G.Action, +bl: Bool, +el: {G.is_legal(g, m) == bl : Bool}, +hi: {L.inv(g) == True{} : Bool}) -> {L.inv(G.play(g, m)) == True{} : Bool}:
  match bl:
    case True{}:
      %Equal.sym(Bool, G.is_legal(g, m), True{}, el) : {L.inv(G.play.go(_, g, m)) == True{} : Bool}
      L.inv_apply(g, m, hi, el)
    case False{}:
      %Equal.sym(Bool, G.is_legal(g, m), False{}, el) : {L.inv(G.play.go(_, g, m)) == True{} : Bool}
      hi

def L.inv_replay(+moves: List<&2, G.Action>, +g: G.Game, +hi: {L.inv(g) == True{} : Bool}) -> {L.inv(G.replay(moves, g)) == True{} : Bool}:
  match moves:
    case Nil{}:
      hi
    case Con{m, rest}:
      L.inv_replay(rest, G.play(g, m), L.inv_play.go(g, m, G.is_legal(g, m), {==}, hi))

# Every game reached by real play keeps the invariant.
def L.inv_after(+setup: G.Setup, +moves: List<&2, G.Action>) -> {L.inv(G.after(setup, moves)) == True{} : Bool}:
  L.inv_replay(moves, G.start(setup), L.inv_start(setup))

# ---------------------------------------------------------------- never_stuck

def L.ns_side.go(+ps: List<&2, G.Piece>, +side: G.Side, +c: U32, +rest: List<&2, U32>, +hv: {L.valid(c) == True{} : Bool}, +hk: {L.keeper(ps, side) == True{} : Bool}, +hc: {Nat.is_le(L.count(ps, side), 7n) == True{} : Bool}, +m: Maybe<&2, G.Cell>, +em: {G.Pieces.teacher_of(ps, side) == m : Maybe<&2, G.Cell>}, +bn: Bool, +en: {G.Actions.nonempty(G.gen.cards(Con{c, rest}, side, ps, Nil{})) == bn : Bool}) -> {G.Actions.nonempty(G.gen.cards(Con{c, rest}, side, ps, Nil{})) == True{} : Bool}:
  match m bn:
    case None{} _:
      Empty.absurd({G.Actions.nonempty(G.gen.cards(Con{c, rest}, side, ps, Nil{})) == True{} : Bool}, L.false_is_not_true({%em : {Bool.not(G.Cell.none(_)) == True{} : Bool}; hk : {False{} == True{} : Bool}}))
    case Some{qk} True{}:
      en
    case Some{qk} False{}:
      Empty.absurd({G.Actions.nonempty(G.gen.cards(Con{c, rest}, side, ps, Nil{})) == True{} : Bool}, L.core(ps, side, c, rest, qk, hv, em, hc, en))

# A side with a valid hand, its goalkeeper and at most 7 pieces has a move.
def L.ns_turn(+ps: List<&2, G.Piece>, +side: G.Side, +hand: List<&2, U32>, +hok: {L.hand_ok(hand) == True{} : Bool}, +hk: {L.keeper(ps, side) == True{} : Bool}, +hc: {Nat.is_le(L.count(ps, side), 7n) == True{} : Bool}) -> {G.Actions.nonempty(G.gen.cards(hand, side, ps, Nil{})) == True{} : Bool}:
  match hand:
    case Nil{}:
      Empty.absurd({G.Actions.nonempty(G.gen.cards(Nil{}, side, ps, Nil{})) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Nil{}}:
      Empty.absurd({G.Actions.nonempty(G.gen.cards(Con{a, Nil{}}, side, ps, Nil{})) == True{} : Bool}, L.false_is_not_true(hok))
    case Con{a, Con{b, Nil{}}}:
      L.ns_side.go(ps, side, a, [b], L.and_l(L.valid(a), L.valid(b), hok), hk, hc, G.Pieces.teacher_of(ps, side), {==}, G.Actions.nonempty(G.gen.cards(Con{a, Con{b, Nil{}}}, side, ps, Nil{})), {==})
    case Con{a, Con{b, Con{d, t}}}:
      Empty.absurd({G.Actions.nonempty(G.gen.cards(Con{a, Con{b, Con{d, t}}}, side, ps, Nil{})) == True{} : Bool}, L.false_is_not_true(hok))

def L.ns_game(+g: G.Game, +hi: {L.inv(g) == True{} : Bool}, +no: {G.is_over(g) == False{} : Bool}) -> {G.has_legal_move(g) == True{} : Bool}:
  match g:
    case G.Game{G.Blue{}, ps, b, r, tb, q, hst, res}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%no : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      %Equal.sym(Bool, G.Outcome.is_over(res), False{}, no) : {G.Actions.nonempty(G.gen.if_ongoing(_, G.Game{G.Blue{}, ps, b, r, tb, q, hst, res})) == True{} : Bool}
      L.ns_turn(ps, G.Blue{}, b, hok_b, L.and_l(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk), hcB)
    case G.Game{G.Red{}, ps, b, r, tb, q, hst, res}:
      +kk = Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))
      +c5 = Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk))
      +c4 = Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5)
      +c3 = Bool.and(L.valid(tb), c4)
      +c2 = Bool.and(L.hand_ok(r), c3)
      +hok_b = L.and_l(L.hand_ok(b), c2, hi)
      +hok_r = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))
      +hcB = L.and_l(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +k6 = L.and_r(Nat.is_le(L.count(ps, G.Blue{}), 7n), c5, L.and_r(L.valid(tb), c4, L.and_r(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), c2, hi))))
      +hcR = L.and_l(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6)
      +hk = {%no : {Bool.or(_, kk) == True{} : Bool}; L.and_r(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), kk), k6) : {kk == True{} : Bool}}
      %Equal.sym(Bool, G.Outcome.is_over(res), False{}, no) : {G.Actions.nonempty(G.gen.if_ongoing(_, G.Game{G.Red{}, ps, b, r, tb, q, hst, res})) == True{} : Bool}
      L.ns_turn(ps, G.Red{}, r, hok_r, L.and_r(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}), hk), hcR)

# Never stuck: in every game reached by real play that is not over, the player to move has a move.
def Laws.never_stuck(setup, moves, not_over):
  L.ns_game(G.after(setup, moves), L.inv_after(setup, moves), not_over)

# ================================================================ group: cards in play

def L.unproven.go(+g: G.Game, +mc: U32, +mf: G.Cell, +mt: G.Cell, +bl: Bool, +el: {G.is_legal(g, G.Action{mc, mf, mt}) == bl : Bool}, +bo: Bool, +eo: {G.Outcome.is_over(G.Game.result(g)) == bo : Bool}, +h: {G.card_proven(g, G.Action{mc, mf, mt}) == False{} : Bool}) -> {G.is_legal(g, G.Action{mc, mf, mt}) == False{} : Bool}:
  match bl bo:
    case False{} _:
      el
    case True{} True{}:
      Empty.absurd({G.is_legal(g, G.Action{mc, mf, mt}) == False{} : Bool}, L.false_is_not_true({%eo : {G.Actions.has(G.gen.if_ongoing(_, g), G.Action{mc, mf, mt}) == True{} : Bool}; el : {False{} == True{} : Bool}}))
    case True{} False{}:
      +hand = G.Game.hand(g, G.Game.turn(g))
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, g), G.Action{mc, mf, mt}) == True{} : Bool}; el : {G.Actions.has(G.gen.cards(hand, G.Game.turn(g), G.Game.pieces(g), Nil{}), G.Action{mc, mf, mt}) == True{} : Bool}}
      +hh = L.or_false_drop(G.U32s.has(hand, mc), L.cards_card(hand, G.Game.turn(g), G.Game.pieces(g), Nil{}, mc, mf, mt, lg))
      Empty.absurd({G.is_legal(g, G.Action{mc, mf, mt}) == False{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, G.U32s.has(hand, mc), False{}, Equal.sym(Bool, G.U32s.has(hand, mc), True{}, hh), h)))

# A move whose card is not in the mover's hand is never legal (in any game).
def L.unproven(+g: G.Game, +m: G.Action, +h: {G.card_proven(g, m) == False{} : Bool}) -> {G.is_legal(g, m) == False{} : Bool}:
  match m:
    case G.Action{mc, mf, mt}:
      L.unproven.go(g, mc, mf, mt, G.is_legal(g, G.Action{mc, mf, mt}), {==}, G.Outcome.is_over(G.Game.result(g)), {==}, h)

def Laws.unproven_card_is_rejected(setup, moves, move, unproven):
  L.unproven(G.after(setup, moves), move, unproven)

def L.len2(+h: List<&2, U32>, +hok: {L.hand_ok(h) == True{} : Bool}) -> {G.U32s.len(h) == 2n : Nat}:
  match h:
    case Nil{}:
      Empty.absurd({G.U32s.len(Nil{}) == 2n : Nat}, L.false_is_not_true(hok))
    case Con{a, Nil{}}:
      Empty.absurd({G.U32s.len(Con{a, Nil{}}) == 2n : Nat}, L.false_is_not_true(hok))
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{d, t}}}:
      Empty.absurd({G.U32s.len(Con{a, Con{b, Con{d, t}}}) == 2n : Nat}, L.false_is_not_true(hok))

def L.five(+g: G.Game, +hi: {L.inv(g) == True{} : Bool}) -> {G.card_count(g) == 5n : Nat}:
  match g:
    case G.Game{turn, ps, b, r, tb, q, hst, res}:
      +c3 = Bool.and(L.valid(tb), Bool.and(Nat.is_le(L.count(ps, G.Blue{}), 7n), Bool.and(Nat.is_le(L.count(ps, G.Red{}), 7n), Bool.or(G.Outcome.is_over(res), Bool.and(L.keeper(ps, G.Blue{}), L.keeper(ps, G.Red{}))))))
      +hb = L.and_l(L.hand_ok(b), Bool.and(L.hand_ok(r), c3), hi)
      +hr = L.and_l(L.hand_ok(r), c3, L.and_r(L.hand_ok(b), Bool.and(L.hand_ok(r), c3), hi))
      %Equal.sym(Nat, G.U32s.len(b), 2n, L.len2(b, hb)) : {Nat.add(Nat.add(_, G.U32s.len(r)), 1n) == 5n : Nat}
      %Equal.sym(Nat, G.U32s.len(r), 2n, L.len2(r, hr)) : {Nat.add(Nat.add(2n, _), 1n) == 5n : Nat}
      {==}

def Laws.always_five_cards(setup, moves):
  +s = setup
  +ms = moves
  L.five(G.after(s, ms), L.inv_after(s, ms))

# ================================================================ group: never on your own piece

def L.add_land.go(+to: G.Cell, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +bs: Bool, +es: {G.Pieces.side_at(ps, to, side) == bs : Bool}, +bm: Bool, +em: {G.Action.same(G.Action{card, from, to}, G.Action{mc, mf, mt}) == bm : Bool}, +h: {G.Actions.has(G.gen.add(G.Pieces.side_at(ps, to, side), G.Action{card, from, to}, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match bs bm:
    case True{} _:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), {%es : {G.Actions.has(G.gen.add(_, G.Action{card, from, to}, acc), G.Action{mc, mf, mt}) == True{} : Bool}; h : {G.Actions.has(acc, G.Action{mc, mf, mt}) == True{} : Bool}})
    case False{} True{}:
      +te = L.and_r(Bool.and(U32.is_eq(card, mc), G.Cell.eq(from, mf)), G.Cell.eq(to, mt), em)
      +nm = {%L.cell_eq_true(to, mt, te) : {G.Pieces.side_at(ps, _, side) == False{} : Bool}; es : {G.Pieces.side_at(ps, mt, side) == False{} : Bool}}
      %Equal.sym(Bool, G.Pieces.side_at(ps, mt, side), False{}, nm) : {Bool.or(Bool.not(_), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}
      {==}
    case False{} False{}:
      +h2 = {%es : {G.Actions.has(G.gen.add(_, G.Action{card, from, to}, acc), G.Action{mc, mf, mt}) == True{} : Bool}; h : {Bool.or(G.Action.same(G.Action{card, from, to}, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}}
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), {%em : {Bool.or(_, G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}; h2 : {G.Actions.has(acc, G.Action{mc, mf, mt}) == True{} : Bool}})

def L.add_to_land(+t: Maybe<&2, G.Cell>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.add_to(t, card, from, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match t:
    case None{}:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Some{to}:
      L.add_land.go(to, card, from, side, ps, acc, mc, mf, mt, G.Pieces.side_at(ps, to, side), {==}, G.Action.same(G.Action{card, from, to}, G.Action{mc, mf, mt}), {==}, h)

def L.steps_land(+sts: List<&2, G.Step>, +card: U32, +from: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.steps(sts, card, from, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match sts:
    case Nil{}:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Con{st, rest}:
      +t = G.Step.target(st, from, side)
      +acc2 = G.gen.add_to(t, card, from, side, ps, acc)
      L.or_step.go(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc2, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt}), Bool.not(G.Pieces.side_at(ps, mt, side)), {==}, L.steps_land(rest, card, from, side, ps, acc2, mc, mf, mt, h), hy => L.add_to_land(t, card, from, side, ps, acc, mc, mf, mt, hy))

def L.one_land(+mine: Bool, +sts: List<&2, G.Step>, +card: U32, +q: G.Cell, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.pieces.one(mine, sts, card, q, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match mine:
    case True{}:
      L.steps_land(sts, card, q, side, ps, acc, mc, mf, mt, h)
    case False{}:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), h)

def L.pieces_land(+it: List<&2, G.Piece>, +card: U32, +sts: List<&2, G.Step>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.pieces(it, card, sts, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match it:
    case Nil{}:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Con{G.Piece{s, t, q}, rest}:
      +acc2 = G.gen.pieces.one(G.Side.same(s, side), sts, card, q, side, ps, acc)
      L.or_step.go(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc2, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt}), Bool.not(G.Pieces.side_at(ps, mt, side)), {==}, L.pieces_land(rest, card, sts, side, ps, acc2, mc, mf, mt, h), hy => L.one_land(G.Side.same(s, side), sts, card, q, side, ps, acc, mc, mf, mt, hy))

def L.cards_land(+hand: List<&2, U32>, +side: G.Side, +ps: List<&2, G.Piece>, +acc: List<&2, G.Action>, +mc: U32, +mf: G.Cell, +mt: G.Cell, +h: {G.Actions.has(G.gen.cards(hand, side, ps, acc), G.Action{mc, mf, mt}) == True{} : Bool}) -> {Bool.or(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt})) == True{} : Bool}:
  match hand:
    case Nil{}:
      L.or_r(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc, G.Action{mc, mf, mt}), h)
    case Con{c, rest}:
      +acc2 = G.gen.pieces(ps, c, G.card_steps(c), side, ps, acc)
      L.or_step.go(Bool.not(G.Pieces.side_at(ps, mt, side)), G.Actions.has(acc2, G.Action{mc, mf, mt}), G.Actions.has(acc, G.Action{mc, mf, mt}), Bool.not(G.Pieces.side_at(ps, mt, side)), {==}, L.cards_land(rest, side, ps, acc2, mc, mf, mt, h), hy => L.pieces_land(ps, c, G.card_steps(c), side, ps, acc, mc, mf, mt, hy))

def L.no_own.go(+g: G.Game, +mc: U32, +mf: G.Cell, +mt: G.Cell, +bo: Bool, +eo: {G.Outcome.is_over(G.Game.result(g)) == bo : Bool}, +legal: {G.is_legal(g, G.Action{mc, mf, mt}) == True{} : Bool}) -> {G.own_at(g, mt) == False{} : Bool}:
  match bo:
    case True{}:
      Empty.absurd({G.own_at(g, mt) == False{} : Bool}, L.false_is_not_true({%eo : {G.Actions.has(G.gen.if_ongoing(_, g), G.Action{mc, mf, mt}) == True{} : Bool}; legal : {False{} == True{} : Bool}}))
    case False{}:
      +ps = G.Game.pieces(g)
      +side = G.Game.turn(g)
      +lg = {%eo : {G.Actions.has(G.gen.if_ongoing(_, g), G.Action{mc, mf, mt}) == True{} : Bool}; legal : {G.Actions.has(G.gen.cards(G.Game.hand(g, side), side, ps, Nil{}), G.Action{mc, mf, mt}) == True{} : Bool}}
      L.not_true(G.Pieces.side_at(ps, mt, side), L.or_false_drop(Bool.not(G.Pieces.side_at(ps, mt, side)), L.cards_land(G.Game.hand(g, side), side, ps, Nil{}, mc, mf, mt, lg)))

# A legal move never lands on one of the mover's pieces (in any game).
def L.no_own(+g: G.Game, +m: G.Action, +legal: {G.is_legal(g, m) == True{} : Bool}) -> {G.own_at(g, G.to_of(m)) == False{} : Bool}:
  match m:
    case G.Action{mc, mf, mt}:
      L.no_own.go(g, mc, mf, mt, G.Outcome.is_over(G.Game.result(g)), {==}, legal)

def Laws.never_lands_on_own_piece(setup, moves, move, legal):
  L.no_own(G.after(setup, moves), move, legal)

# ================================================================ group: draws
# Invariant: the result always agrees with the history and the quiet count (Game.drawn).

def L.dinv.of(o: G.Outcome, +h: List<&2, U32>, +q: Nat) -> Bool:
  match o:
    case G.Ongoing{}:
      Bool.not(G.Game.drawn(h, q))
    case G.Draw{}:
      G.Game.drawn(h, q)
    case G.Winner{_}:
      True{}

def L.dinv(g: G.Game) -> Bool:
  match g:
    case G.Game{turn, ps, b, r, tb, q, h, res}:
      L.dinv.of(res, h, q)

def L.dinv_dealt(+starter: G.Side, +d: G.Deal) -> {L.dinv(G.start_dealt(starter, d)) == True{} : Bool}:
  match d:
    case G.Deal{b, r, t}:
      +k0 = G.Game.key(G.Pieces.start(), b, r, t, starter)
      %Equal.sym(Bool, U32.is_eq(k0, k0), True{}, L.u32_eq_refl(k0)) : {Bool.not(Bool.or(Nat.is_ge(G.U32s.count.add(_, 0n), 3n), Nat.is_ge(0n, 20n))) == True{} : Bool}
      {==}

def L.dinv_start(+setup: G.Setup) -> {L.dinv(G.start(setup)) == True{} : Bool}:
  L.dinv_dealt(G.Setup.starter(setup), G.Setup.deal(setup))

def L.dinv_draw(+turn: G.Side, +h: List<&2, U32>, +q: Nat, +bd: Bool, +ed: {G.Game.drawn(h, q) == bd : Bool}) -> {L.dinv.of(G.outcome_after(False{}, turn, G.Game.drawn(h, q)), h, q) == True{} : Bool}:
  match bd:
    case True{}:
      %Equal.sym(Bool, G.Game.drawn(h, q), True{}, ed) : {L.dinv.of(G.outcome_after(False{}, turn, _), h, q) == True{} : Bool}
      ed
    case False{}:
      %Equal.sym(Bool, G.Game.drawn(h, q), False{}, ed) : {L.dinv.of(G.outcome_after(False{}, turn, _), h, q) == True{} : Bool}
      L.not_false(G.Game.drawn(h, q), ed)

def L.dinv_apply.go(+turn: G.Side, +ps: List<&2, G.Piece>, +b: List<&2, U32>, +r: List<&2, U32>, +tb: U32, +q: Nat, +hst: List<&2, U32>, +c: U32, +f: G.Cell, +to: G.Cell, +bw: Bool, +ew: {G.won(ps, G.Side.other(turn), to) == bw : Bool}) -> {L.dinv(G.apply.go(G.won(ps, G.Side.other(turn), to), turn, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}:
  match bw:
    case True{}:
      %Equal.sym(Bool, G.won(ps, G.Side.other(turn), to), True{}, ew) : {L.dinv(G.apply.go(_, turn, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, G.won(ps, G.Side.other(turn), to), False{}, ew) : {L.dinv(G.apply.go(_, turn, ps, b, r, tb, q, hst, c, f, to)) == True{} : Bool}
      +g2 = G.apply.go(False{}, turn, ps, b, r, tb, q, hst, c, f, to)
      L.dinv_draw(turn, G.Game.history(g2), G.Game.quiet(g2), G.Game.drawn(G.Game.history(g2), G.Game.quiet(g2)), {==})


def L.dinv_apply(+g: G.Game, +m: G.Action) -> {L.dinv(G.apply(g, m)) == True{} : Bool}:
  match g m:
    case G.Game{turn, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      L.dinv_apply.go(turn, ps, b, r, tb, q, hst, c, f, to, G.won(ps, G.Side.other(turn), to), {==})

def L.dinv_play.go(+g: G.Game, +m: G.Action, +bl: Bool, +el: {G.is_legal(g, m) == bl : Bool}, +hi: {L.dinv(g) == True{} : Bool}) -> {L.dinv(G.play(g, m)) == True{} : Bool}:
  match bl:
    case True{}:
      %Equal.sym(Bool, G.is_legal(g, m), True{}, el) : {L.dinv(G.play.go(_, g, m)) == True{} : Bool}
      L.dinv_apply(g, m)
    case False{}:
      %Equal.sym(Bool, G.is_legal(g, m), False{}, el) : {L.dinv(G.play.go(_, g, m)) == True{} : Bool}
      hi

def L.dinv_replay(+moves: List<&2, G.Action>, +g: G.Game, +hi: {L.dinv(g) == True{} : Bool}) -> {L.dinv(G.replay(moves, g)) == True{} : Bool}:
  match moves:
    case Nil{}:
      hi
    case Con{m, rest}:
      L.dinv_replay(rest, G.play(g, m), L.dinv_play.go(g, m, G.is_legal(g, m), {==}, hi))

def L.dinv_after(+setup: G.Setup, +moves: List<&2, G.Action>) -> {L.dinv(G.after(setup, moves)) == True{} : Bool}:
  L.dinv_replay(moves, G.start(setup), L.dinv_start(setup))

def L.three(+g: G.Game, +hd: {L.dinv(g) == True{} : Bool}, +rep: {Nat.is_ge(G.U32s.count(G.Game.history(g), G.U32s.nth(G.Game.history(g), 0n)), 3n) == True{} : Bool}, +nw: {G.has_winner(g) == False{} : Bool}) -> {G.outcome(g) == G.Draw{} : G.Outcome}:
  match g:
    case G.Game{turn, ps, b, r, tb, q, hst, G.Ongoing{}}:
      +rp = Nat.is_ge(G.U32s.count(hst, G.U32s.nth(hst, 0n)), 3n)
      +nd = L.not_true(G.Game.drawn(hst, q), hd)
      Empty.absurd({G.Ongoing{} == G.Draw{} : G.Outcome}, L.true_is_not_false(Equal.trans(Bool, True{}, rp, False{}, Equal.sym(Bool, rp, True{}, rep), L.or_false_l(rp, Nat.is_ge(q, 20n), nd))))
    case G.Game{turn, ps, b, r, tb, q, hst, G.Draw{}}:
      {==}
    case G.Game{turn, ps, b, r, tb, q, hst, G.Winner{s}}:
      Empty.absurd({G.Winner{s} == G.Draw{} : G.Outcome}, L.true_is_not_false(nw))

def Laws.threefold_repetition_draws(setup, moves, repeated, no_winner):
  L.three(G.after(setup, moves), L.dinv_after(setup, moves), repeated, no_winner)

def L.twenty(+g: G.Game, +hd: {L.dinv(g) == True{} : Bool}, +qt: {Nat.is_ge(G.Game.quiet(g), 20n) == True{} : Bool}, +nw: {G.has_winner(g) == False{} : Bool}) -> {G.outcome(g) == G.Draw{} : G.Outcome}:
  match g:
    case G.Game{turn, ps, b, r, tb, q, hst, G.Ongoing{}}:
      +rp = Nat.is_ge(G.U32s.count(hst, G.U32s.nth(hst, 0n)), 3n)
      +nd = L.not_true(G.Game.drawn(hst, q), hd)
      Empty.absurd({G.Ongoing{} == G.Draw{} : G.Outcome}, L.true_is_not_false(Equal.trans(Bool, True{}, Nat.is_ge(q, 20n), False{}, Equal.sym(Bool, Nat.is_ge(q, 20n), True{}, qt), L.or_false_r(rp, Nat.is_ge(q, 20n), nd))))
    case G.Game{turn, ps, b, r, tb, q, hst, G.Draw{}}:
      {==}
    case G.Game{turn, ps, b, r, tb, q, hst, G.Winner{s}}:
      Empty.absurd({G.Winner{s} == G.Draw{} : G.Outcome}, L.true_is_not_false(nw))

def Laws.twenty_quiet_turns_draw(setup, moves, quiet, no_winner):
  L.twenty(G.after(setup, moves), L.dinv_after(setup, moves), quiet, no_winner)

def L.donly(+g: G.Game, +hd: {L.dinv(g) == True{} : Bool}, +e: {G.outcome(g) == G.Draw{} : G.Outcome}) -> {G.Game.drawn(G.Game.history(g), G.Game.quiet(g)) == True{} : Bool}:
  match g:
    case G.Game{turn, ps, b, r, tb, q, hst, res}:
      {%e : {L.dinv.of(_, hst, q) == True{} : Bool}; hd : {G.Game.drawn(hst, q) == True{} : Bool}}

def Laws.draw_only_by_rule(setup, moves, drawn):
  L.donly(G.after(setup, moves), L.dinv_after(setup, moves), drawn)

# ================================================================ group: captures
# Invariant: no two pieces share a square.

def L.cells(ps: List<&2, G.Piece>) -> List<&2, G.Cell>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{G.Piece{s, t, q}, rest}:
      q <> L.cells(rest)

def L.hit_false(+s: G.Side, +e: G.Side, +x: Bool, +hx: {x == False{} : Bool}) -> {Bool.and(G.Side.same(s, e), x) == False{} : Bool}:
  match s e:
    case G.Blue{} G.Blue{}:
      %Equal.sym(Bool, x, False{}, hx) : {Bool.and(G.Side.same(G.Blue{}, G.Blue{}), _) == False{} : Bool}
      {==}
    case G.Blue{} G.Red{}:
      %Equal.sym(Bool, x, False{}, hx) : {Bool.and(G.Side.same(G.Blue{}, G.Red{}), _) == False{} : Bool}
      {==}
    case G.Red{} G.Blue{}:
      %Equal.sym(Bool, x, False{}, hx) : {Bool.and(G.Side.same(G.Red{}, G.Blue{}), _) == False{} : Bool}
      {==}
    case G.Red{} G.Red{}:
      %Equal.sym(Bool, x, False{}, hx) : {Bool.and(G.Side.same(G.Red{}, G.Red{}), _) == False{} : Bool}
      {==}

def L.cap_sub.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +c: G.Cell, +b: Bool, +eb: {Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)) == b : Bool}, +h: {G.Cells.has(L.cells(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, to, e)), c) == True{} : Bool}, ih: {G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), c) == True{} : Bool} -> {G.Cells.has(L.cells(rest), c) == True{} : Bool}) -> {G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c) == True{} : Bool}:
  match b:
    case True{}:
      L.or_r(G.Cell.eq(q, c), G.Cells.has(L.cells(rest), c), ih({%eb : {G.Cells.has(L.cells(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))), c) == True{} : Bool}; h : {G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), c) == True{} : Bool}}))
    case False{}:
      +h2 = {%eb : {G.Cells.has(L.cells(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))), c) == True{} : Bool}; h : {Bool.or(G.Cell.eq(q, c), G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), c)) == True{} : Bool}}
      L.or_step.go(G.Cell.eq(q, c), G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), c), G.Cells.has(L.cells(rest), c), G.Cell.eq(q, c), {==}, h2, hy => L.or_r(G.Cell.eq(q, c), G.Cells.has(L.cells(rest), c), ih(hy)))

# Capturing only removes squares.
def L.cap_sub(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +c: G.Cell, +h: {G.Cells.has(L.cells(G.Pieces.capture(ps, to, e)), c) == True{} : Bool}) -> {G.Cells.has(L.cells(ps), c) == True{} : Bool}:
  match ps:
    case Nil{}:
      h
    case Con{G.Piece{s, t, q}, rest}:
      L.cap_sub.go(s, t, q, rest, to, e, c, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), {==}, h, h2 => L.cap_sub(rest, to, e, c, h2))

def L.not_in.go(-x: Bool, -y: Bool, +b: Bool, +eb: {x == b : Bool}, k: {x == True{} : Bool} -> {y == True{} : Bool}, +hy: {y == False{} : Bool}) -> {x == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({x == False{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, y, False{}, Equal.sym(Bool, y, True{}, k(eb)), hy)))

def L.or_l(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def L.add_one(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, L.add_one(p)) : {1n+_ == 1n+1n+p : Nat}
      {==}

def L.cap_dist.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +b: Bool, +eb: {Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)) == b : Bool}, +d: {Bool.and(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest))) == True{} : Bool}, +ih: {L.distinct(L.cells(G.Pieces.capture(rest, to, e))) == True{} : Bool}) -> {L.distinct(L.cells(G.Pieces.capture.go(Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), True{}, eb) : {L.distinct(L.cells(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e)))) == True{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), False{}, eb) : {L.distinct(L.cells(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e)))) == True{} : Bool}
      +hy = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +nin = L.not_in.go(G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), q), G.Cells.has(L.cells(rest), q), G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), q), {==}, h2 => L.cap_sub(rest, to, e, q, h2), hy)
      L.and2(Bool.not(G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), q)), L.distinct(L.cells(G.Pieces.capture(rest, to, e))), L.not_false(G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), q), nin), ih)

def L.cap_dist(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +d: {L.distinct(L.cells(ps)) == True{} : Bool}) -> {L.distinct(L.cells(G.Pieces.capture(ps, to, e))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.cap_dist.go(s, t, q, rest, to, e, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), {==}, d, L.cap_dist(rest, to, e, L.and_r(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d)))

# With no piece on `to`, capturing there removes nothing.
def L.cap_none(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +nh: {G.Cells.has(L.cells(ps), to) == False{} : Bool}) -> {G.Pieces.len(G.Pieces.capture(ps, to, e)) == G.Pieces.len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      +hq = L.or_false_l(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to), nh)
      +hr = L.or_false_r(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to), nh)
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), False{}, L.hit_false(s, e, G.Cell.eq(q, to), hq)) : {G.Pieces.len(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.capture(rest, to, e)), G.Pieces.len(rest), L.cap_none(rest, to, e, hr)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}

def L.code_side_f(+s: G.Side, +t: Bool, +side: G.Side, +h: {G.Code.is_side(G.Piece.code(s, t), side) == False{} : Bool}) -> {G.Side.same(s, side) == False{} : Bool}:
  match s t side:
    case G.Blue{} True{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Blue{}) == False{} : Bool}, L.true_is_not_false(h))
    case G.Blue{} True{} G.Red{}:
      {==}
    case G.Blue{} False{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Blue{}) == False{} : Bool}, L.true_is_not_false(h))
    case G.Blue{} False{} G.Red{}:
      {==}
    case G.Red{} True{} G.Blue{}:
      {==}
    case G.Red{} True{} G.Red{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Red{}) == False{} : Bool}, L.true_is_not_false(h))
    case G.Red{} False{} G.Blue{}:
      {==}
    case G.Red{} False{} G.Red{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Red{}) == False{} : Bool}, L.true_is_not_false(h))

def L.third(+s: G.Side, +a: G.Side, +e: G.Side, +h1: {G.Side.same(s, a) == False{} : Bool}, +h2: {G.Side.same(a, e) == False{} : Bool}) -> {G.Side.same(s, e) == True{} : Bool}:
  match s a e:
    case G.Blue{} G.Blue{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Blue{}) == True{} : Bool}, L.true_is_not_false(h1))
    case G.Blue{} G.Blue{} G.Red{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Red{}) == True{} : Bool}, L.true_is_not_false(h1))
    case G.Blue{} G.Red{} G.Blue{}:
      {==}
    case G.Blue{} G.Red{} G.Red{}:
      Empty.absurd({G.Side.same(G.Blue{}, G.Red{}) == True{} : Bool}, L.true_is_not_false(h2))
    case G.Red{} G.Blue{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Blue{}) == True{} : Bool}, L.true_is_not_false(h2))
    case G.Red{} G.Blue{} G.Red{}:
      {==}
    case G.Red{} G.Red{} G.Blue{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Blue{}) == True{} : Bool}, L.true_is_not_false(h1))
    case G.Red{} G.Red{} G.Red{}:
      Empty.absurd({G.Side.same(G.Red{}, G.Red{}) == True{} : Bool}, L.true_is_not_false(h1))

def L.side_at_head(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +side: G.Side, +b: Bool, +eb: {G.Cell.eq(q, to) == b : Bool}) -> {G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, side) == G.Code.is_side(G.sel(b, G.Piece.code(s, t), G.Pieces.code_at(rest, to)), side) : Bool}:
  %Equal.sym(Bool, G.Cell.eq(q, to), b, eb) : {G.Code.is_side(G.sel(_, G.Piece.code(s, t), G.Pieces.code_at(rest, to)), side) == G.Code.is_side(G.sel(b, G.Piece.code(s, t), G.Pieces.code_at(rest, to)), side) : Bool}
  {==}

def L.cap_one.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +b: Bool, +eb: {G.Cell.eq(q, to) == b : Bool}, +d: {Bool.and(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest))) == True{} : Bool}, +h: {G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e) == True{} : Bool}, ih: {G.Pieces.side_at(rest, to, e) == True{} : Bool} -> {1n+G.Pieces.len(G.Pieces.capture(rest, to, e)) == G.Pieces.len(rest) : Nat}) -> {1n+G.Pieces.len(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, to, e)) == G.Pieces.len(Con{G.Piece{s, t, q}, rest}) : Nat}:
  match b:
    case True{}:
      +hs = L.code_side(s, t, e, Equal.trans(Bool, G.Code.is_side(G.Piece.code(s, t), e), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), True{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), G.Code.is_side(G.Piece.code(s, t), e), L.side_at_head(s, t, q, rest, to, e, True{}, eb)), h))
      %Equal.sym(Bool, G.Side.same(s, e), True{}, hs) : {1n+G.Pieces.len(G.Pieces.capture.go(Bool.and(_, G.Cell.eq(q, to)), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      %Equal.sym(Bool, G.Cell.eq(q, to), True{}, eb) : {1n+G.Pieces.len(G.Pieces.capture.go(Bool.and(True{}, _), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      +nq = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +nt = {%L.cell_eq_true(q, to, eb) : {G.Cells.has(L.cells(rest), _) == False{} : Bool}; nq : {G.Cells.has(L.cells(rest), to) == False{} : Bool}}
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.capture(rest, to, e)), G.Pieces.len(rest), L.cap_none(rest, to, e, nt)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}
    case False{}:
      +hr = Equal.trans(Bool, G.Pieces.side_at(rest, to, e), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), True{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), G.Pieces.side_at(rest, to, e), L.side_at_head(s, t, q, rest, to, e, False{}, eb)), h)
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), False{}, L.hit_false(s, e, G.Cell.eq(q, to), eb)) : {1n+G.Pieces.len(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      %ih(hr) : {1n+1n+G.Pieces.len(G.Pieces.capture(rest, to, e)) == 1n+_ : Nat}
      {==}

# Landing on an enemy square removes exactly one piece (squares are never shared).
def L.cap_one(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +d: {L.distinct(L.cells(ps)) == True{} : Bool}, +h: {G.Pieces.side_at(ps, to, e) == True{} : Bool}) -> {1n+G.Pieces.len(G.Pieces.capture(ps, to, e)) == G.Pieces.len(ps) : Nat}:
  match ps:
    case Nil{}:
      match e:
        case G.Blue{}:
          Empty.absurd({1n+0n == 0n : Nat}, L.false_is_not_true(h))
        case G.Red{}:
          Empty.absurd({1n+0n == 0n : Nat}, L.false_is_not_true(h))
    case Con{G.Piece{s, t, q}, rest}:
      L.cap_one.go(s, t, q, rest, to, e, G.Cell.eq(q, to), {==}, d, h, h2 => L.cap_one(rest, to, e, L.and_r(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d), h2))

def L.cap_keep.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +b: Bool, +eb: {G.Cell.eq(q, to) == b : Bool}, +d: {Bool.and(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest))) == True{} : Bool}, +h: {G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e) == False{} : Bool}, ih: {G.Pieces.side_at(rest, to, e) == False{} : Bool} -> {G.Pieces.len(G.Pieces.capture(rest, to, e)) == G.Pieces.len(rest) : Nat}) -> {G.Pieces.len(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, to, e)) == G.Pieces.len(Con{G.Piece{s, t, q}, rest}) : Nat}:
  match b:
    case True{}:
      +hs = L.code_side_f(s, t, e, Equal.trans(Bool, G.Code.is_side(G.Piece.code(s, t), e), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), False{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), G.Code.is_side(G.Piece.code(s, t), e), L.side_at_head(s, t, q, rest, to, e, True{}, eb)), h))
      %Equal.sym(Bool, G.Side.same(s, e), False{}, hs) : {G.Pieces.len(G.Pieces.capture.go(Bool.and(_, G.Cell.eq(q, to)), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      +nq = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +nt = {%L.cell_eq_true(q, to, eb) : {G.Cells.has(L.cells(rest), _) == False{} : Bool}; nq : {G.Cells.has(L.cells(rest), to) == False{} : Bool}}
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.capture(rest, to, e)), G.Pieces.len(rest), L.cap_none(rest, to, e, nt)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}
    case False{}:
      +hr = Equal.trans(Bool, G.Pieces.side_at(rest, to, e), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), False{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, e), G.Pieces.side_at(rest, to, e), L.side_at_head(s, t, q, rest, to, e, False{}, eb)), h)
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), False{}, L.hit_false(s, e, G.Cell.eq(q, to), eb)) : {G.Pieces.len(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))) == 1n+G.Pieces.len(rest) : Nat}
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.capture(rest, to, e)), G.Pieces.len(rest), ih(hr)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}

# Landing on a square with no enemy removes nothing.
def L.cap_keep(+ps: List<&2, G.Piece>, +to: G.Cell, +e: G.Side, +d: {L.distinct(L.cells(ps)) == True{} : Bool}, +h: {G.Pieces.side_at(ps, to, e) == False{} : Bool}) -> {G.Pieces.len(G.Pieces.capture(ps, to, e)) == G.Pieces.len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.cap_keep.go(s, t, q, rest, to, e, G.Cell.eq(q, to), {==}, d, h, h2 => L.cap_keep(rest, to, e, L.and_r(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d), h2))

def L.cap_clear.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +to: G.Cell, +a: G.Side, +e: G.Side, +ne: {G.Side.same(a, e) == False{} : Bool}, +b: Bool, +eb: {G.Cell.eq(q, to) == b : Bool}, +d: {Bool.and(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest))) == True{} : Bool}, +no: {G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, a) == False{} : Bool}, ih: {G.Pieces.side_at(rest, to, a) == False{} : Bool} -> {G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), to) == False{} : Bool}) -> {G.Cells.has(L.cells(G.Pieces.capture(Con{G.Piece{s, t, q}, rest}, to, e)), to) == False{} : Bool}:
  match b:
    case True{}:
      +ns = L.code_side_f(s, t, a, Equal.trans(Bool, G.Code.is_side(G.Piece.code(s, t), a), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, a), False{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, a), G.Code.is_side(G.Piece.code(s, t), a), L.side_at_head(s, t, q, rest, to, a, True{}, eb)), no))
      %Equal.sym(Bool, G.Side.same(s, e), True{}, L.third(s, a, e, ns, ne)) : {G.Cells.has(L.cells(G.Pieces.capture.go(Bool.and(_, G.Cell.eq(q, to)), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))), to) == False{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, to), True{}, eb) : {G.Cells.has(L.cells(G.Pieces.capture.go(Bool.and(True{}, _), G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))), to) == False{} : Bool}
      +nq = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +nt = {%L.cell_eq_true(q, to, eb) : {G.Cells.has(L.cells(rest), _) == False{} : Bool}; nq : {G.Cells.has(L.cells(rest), to) == False{} : Bool}}
      L.not_in.go(G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), to), G.Cells.has(L.cells(rest), to), G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), to), {==}, h2 => L.cap_sub(rest, to, e, to, h2), nt)
    case False{}:
      +hr = Equal.trans(Bool, G.Pieces.side_at(rest, to, a), G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, a), False{}, Equal.sym(Bool, G.Pieces.side_at(Con{G.Piece{s, t, q}, rest}, to, a), G.Pieces.side_at(rest, to, a), L.side_at_head(s, t, q, rest, to, a, False{}, eb)), no)
      %Equal.sym(Bool, Bool.and(G.Side.same(s, e), G.Cell.eq(q, to)), False{}, L.hit_false(s, e, G.Cell.eq(q, to), eb)) : {G.Cells.has(L.cells(G.Pieces.capture.go(_, G.Piece{s, t, q}, G.Pieces.capture(rest, to, e))), to) == False{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, to), False{}, eb) : {Bool.or(_, G.Cells.has(L.cells(G.Pieces.capture(rest, to, e)), to)) == False{} : Bool}
      ih(hr)

# After capturing the enemy on `to`, nothing stands there (the mover had no piece there).
def L.cap_clear(+ps: List<&2, G.Piece>, +to: G.Cell, +a: G.Side, +e: G.Side, +ne: {G.Side.same(a, e) == False{} : Bool}, +d: {L.distinct(L.cells(ps)) == True{} : Bool}, +no: {G.Pieces.side_at(ps, to, a) == False{} : Bool}) -> {G.Cells.has(L.cells(G.Pieces.capture(ps, to, e)), to) == False{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      L.cap_clear.go(s, t, q, rest, to, a, e, ne, G.Cell.eq(q, to), {==}, d, no, h2 => L.cap_clear(rest, to, a, e, ne, L.and_r(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d), h2))


def L.move_mem.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +c: G.Cell, +bf: Bool, +ef: {G.Cell.eq(q, f) == bf : Bool}, +bc: Bool, +ec: {G.Cell.eq(G.Cell.sel(bf, to, q), c) == bc : Bool}, +h: {G.Cells.has(L.cells(G.Pieces.move(Con{G.Piece{s, t, q}, rest}, f, to)), c) == True{} : Bool}, ih: {G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c) == True{} : Bool} -> {Bool.or(G.Cells.has(L.cells(rest), c), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(rest), f))) == True{} : Bool}) -> {Bool.or(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), f))) == True{} : Bool}:
  match bf bc:
    case True{} True{}:
      %Equal.sym(Bool, G.Cell.eq(q, f), True{}, ef) : {Bool.or(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c), Bool.and(G.Cell.eq(to, c), Bool.or(_, G.Cells.has(L.cells(rest), f)))) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(to, c), True{}, ec) : {Bool.or(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c), Bool.and(_, True{})) == True{} : Bool}
      L.or_true_r(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c))
    case True{} False{}:
      +h1 = {%ef : {Bool.or(G.Cell.eq(G.Cell.sel(_, to, q), c), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}; h : {Bool.or(G.Cell.eq(to, c), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}}
      +h2 = {%ec : {Bool.or(_, G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}; h1 : {G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c) == True{} : Bool}}
      +h3 = {%ec : {Bool.or(G.Cells.has(L.cells(rest), c), Bool.and(_, G.Cells.has(L.cells(rest), f))) == True{} : Bool}; ih(h2) : {Bool.or(G.Cells.has(L.cells(rest), c), False{}) == True{} : Bool}}
      L.or_l(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), f)), L.or_r(G.Cell.eq(q, c), G.Cells.has(L.cells(rest), c), L.or_false_drop(G.Cells.has(L.cells(rest), c), h3)))
    case False{} True{}:
      L.or_l(G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), c), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), f)), L.or_l(G.Cell.eq(q, c), G.Cells.has(L.cells(rest), c), ec))
    case False{} False{}:
      +h1 = {%ef : {Bool.or(G.Cell.eq(G.Cell.sel(_, to, q), c), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}; h : {Bool.or(G.Cell.eq(q, c), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}}
      +h2 = {%ec : {Bool.or(_, G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c)) == True{} : Bool}; h1 : {G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), c) == True{} : Bool}}
      %Equal.sym(Bool, G.Cell.eq(q, c), False{}, ec) : {Bool.or(Bool.or(_, G.Cells.has(L.cells(rest), c)), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(Con{G.Piece{s, t, q}, rest}), f))) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(q, f), False{}, ef) : {Bool.or(G.Cells.has(L.cells(rest), c), Bool.and(G.Cell.eq(to, c), Bool.or(_, G.Cells.has(L.cells(rest), f)))) == True{} : Bool}
      ih(h2)

# A square after a move was there before, or it is `to` and the moved piece came from `f`.
def L.move_mem(+xs: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +c: G.Cell, +h: {G.Cells.has(L.cells(G.Pieces.move(xs, f, to)), c) == True{} : Bool}) -> {Bool.or(G.Cells.has(L.cells(xs), c), Bool.and(G.Cell.eq(to, c), G.Cells.has(L.cells(xs), f))) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.or(False{}, Bool.and(G.Cell.eq(to, c), False{})) == True{} : Bool}, L.false_is_not_true(h))
    case Con{G.Piece{s, t, q}, rest}:
      L.move_mem.go(s, t, q, rest, f, to, c, G.Cell.eq(q, f), {==}, G.Cell.eq(G.Cell.sel(G.Cell.eq(q, f), to, q), c), {==}, h, h2 => L.move_mem(rest, f, to, c, h2))


def L.oaf1(+a: Bool, +e: Bool, +b: Bool, +ha: {a == False{} : Bool}, +he: {e == True{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, Bool.and(e, b)) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, Bool.and(e, b)) == False{} : Bool}
  %Equal.sym(Bool, e, True{}, he) : {Bool.and(_, b) == False{} : Bool}
  hb

def L.oaf2(+a: Bool, +e: Bool, +b: Bool, +ha: {a == False{} : Bool}, +he: {e == False{} : Bool}) -> {Bool.or(a, Bool.and(e, b)) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, Bool.and(e, b)) == False{} : Bool}
  %Equal.sym(Bool, e, False{}, he) : {Bool.and(_, b) == False{} : Bool}
  {==}

def L.move_dist.go(+s: G.Side, +t: Bool, +q: G.Cell, +rest: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +bf: Bool, +ef: {G.Cell.eq(q, f) == bf : Bool}, +d: {Bool.and(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest))) == True{} : Bool}, +nt: {Bool.or(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to)) == False{} : Bool}, +ih: {L.distinct(L.cells(G.Pieces.move(rest, f, to))) == True{} : Bool}) -> {L.distinct(L.cells(G.Pieces.move(Con{G.Piece{s, t, q}, rest}, f, to))) == True{} : Bool}:
  match bf:
    case True{}:
      %Equal.sym(Bool, G.Cell.eq(q, f), True{}, ef) : {Bool.and(Bool.not(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), G.Cell.sel(_, to, q))), L.distinct(L.cells(G.Pieces.move(rest, f, to)))) == True{} : Bool}
      +nq = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +ntr = L.or_false_r(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to), nt)
      +nf = {%L.cell_eq_true(q, f, ef) : {G.Cells.has(L.cells(rest), _) == False{} : Bool}; nq : {G.Cells.has(L.cells(rest), f) == False{} : Bool}}
      +hy = L.oaf1(G.Cells.has(L.cells(rest), to), G.Cell.eq(to, to), G.Cells.has(L.cells(rest), f), ntr, L.cell_refl(to), nf)
      +nin = L.not_in.go(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), to), Bool.or(G.Cells.has(L.cells(rest), to), Bool.and(G.Cell.eq(to, to), G.Cells.has(L.cells(rest), f))), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), to), {==}, h2 => L.move_mem(rest, f, to, to, h2), hy)
      L.and2(Bool.not(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), to)), L.distinct(L.cells(G.Pieces.move(rest, f, to))), L.not_false(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), to), nin), ih)
    case False{}:
      %Equal.sym(Bool, G.Cell.eq(q, f), False{}, ef) : {Bool.and(Bool.not(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), G.Cell.sel(_, to, q))), L.distinct(L.cells(G.Pieces.move(rest, f, to)))) == True{} : Bool}
      +nq = L.not_true(G.Cells.has(L.cells(rest), q), L.and_l(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d))
      +neq = Equal.trans(Bool, G.Cell.eq(to, q), G.Cell.eq(q, to), False{}, L.cell_eq_sym(to, q), L.or_false_l(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to), nt))
      +hy = L.oaf2(G.Cells.has(L.cells(rest), q), G.Cell.eq(to, q), G.Cells.has(L.cells(rest), f), nq, neq)
      +nin = L.not_in.go(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), q), Bool.or(G.Cells.has(L.cells(rest), q), Bool.and(G.Cell.eq(to, q), G.Cells.has(L.cells(rest), f))), G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), q), {==}, h2 => L.move_mem(rest, f, to, q, h2), hy)
      L.and2(Bool.not(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), q)), L.distinct(L.cells(G.Pieces.move(rest, f, to))), L.not_false(G.Cells.has(L.cells(G.Pieces.move(rest, f, to)), q), nin), ih)

# Moving onto an empty square keeps squares unshared.
def L.move_dist(+xs: List<&2, G.Piece>, +f: G.Cell, +to: G.Cell, +d: {L.distinct(L.cells(xs)) == True{} : Bool}, +nt: {G.Cells.has(L.cells(xs), to) == False{} : Bool}) -> {L.distinct(L.cells(G.Pieces.move(xs, f, to))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      +dr = L.and_r(Bool.not(G.Cells.has(L.cells(rest), q)), L.distinct(L.cells(rest)), d)
      L.move_dist.go(s, t, q, rest, f, to, G.Cell.eq(q, f), {==}, d, nt, L.move_dist(rest, f, to, dr, L.or_false_r(G.Cell.eq(q, to), G.Cells.has(L.cells(rest), to), nt)))

# ---- the invariant: no shared squares, in every reachable game

def L.pinv(g: G.Game) -> Bool:
  L.distinct(L.cells(G.Game.pieces(g)))

def L.ne_other(+a: G.Side) -> {G.Side.same(a, G.Side.other(a)) == False{} : Bool}:
  match a:
    case G.Blue{}:
      {==}
    case G.Red{}:
      {==}

def L.pinv_dealt(+starter: G.Side, +d: G.Deal) -> {L.pinv(G.start_dealt(starter, d)) == True{} : Bool}:
  match d:
    case G.Deal{b, r, t}:
      {==}

def L.pinv_apply.go(+g: G.Game, +m: G.Action, +hp: {L.pinv(g) == True{} : Bool}, +no: {G.own_at(g, G.to_of(m)) == False{} : Bool}) -> {L.pinv(G.apply(g, m)) == True{} : Bool}:
  match g m:
    case G.Game{turn, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      +e = G.Side.other(turn)
      L.move_dist(G.Pieces.capture(ps, to, e), f, to, L.cap_dist(ps, to, e, hp), L.cap_clear(ps, to, turn, e, L.ne_other(turn), hp, no))

def L.pinv_apply(+g: G.Game, +m: G.Action, +hp: {L.pinv(g) == True{} : Bool}, +legal: {G.is_legal(g, m) == True{} : Bool}) -> {L.pinv(G.apply(g, m)) == True{} : Bool}:
  L.pinv_apply.go(g, m, hp, L.no_own(g, m, legal))

def L.pinv_play.go(+g: G.Game, +m: G.Action, +bl: Bool, +el: {G.is_legal(g, m) == bl : Bool}, +hi: {L.pinv(g) == True{} : Bool}) -> {L.pinv(G.play(g, m)) == True{} : Bool}:
  match bl:
    case True{}:
      %Equal.sym(Bool, G.is_legal(g, m), True{}, el) : {L.pinv(G.play.go(_, g, m)) == True{} : Bool}
      L.pinv_apply(g, m, hi, el)
    case False{}:
      %Equal.sym(Bool, G.is_legal(g, m), False{}, el) : {L.pinv(G.play.go(_, g, m)) == True{} : Bool}
      hi

def L.pinv_replay(+moves: List<&2, G.Action>, +g: G.Game, +hi: {L.pinv(g) == True{} : Bool}) -> {L.pinv(G.replay(moves, g)) == True{} : Bool}:
  match moves:
    case Nil{}:
      hi
    case Con{m, rest}:
      L.pinv_replay(rest, G.play(g, m), L.pinv_play.go(g, m, G.is_legal(g, m), {==}, hi))

def L.pinv_after(+setup: G.Setup, +moves: List<&2, G.Action>) -> {L.pinv(G.after(setup, moves)) == True{} : Bool}:
  L.pinv_replay(moves, G.start(setup), L.pinv_dealt(G.Setup.starter(setup), G.Setup.deal(setup)))

def L.landing.go(+g: G.Game, +m: G.Action, +hp: {L.pinv(g) == True{} : Bool}, +en: {G.enemy_at(g, G.to_of(m)) == True{} : Bool}) -> {Nat.add(G.piece_count(G.apply(g, m)), 1n) == G.piece_count(g) : Nat}:
  match g m:
    case G.Game{turn, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      +cp = G.Pieces.capture(ps, to, G.Side.other(turn))
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.move(cp, f, to)), G.Pieces.len(cp), L.len_move(cp, f, to)) : {Nat.add(_, 1n) == G.Pieces.len(ps) : Nat}
      %Equal.sym(Nat, Nat.add(G.Pieces.len(cp), 1n), 1n+G.Pieces.len(cp), L.add_one(G.Pieces.len(cp))) : {_ == G.Pieces.len(ps) : Nat}
      L.cap_one(ps, to, G.Side.other(turn), hp, en)

def Laws.landing_on_enemy_captures(setup, moves, move, legal, enemy):
  +g = G.after(setup, moves)
  %Equal.sym(Bool, G.is_legal(g, move), True{}, legal) : {Nat.add(G.piece_count(G.play.go(_, g, move)), 1n) == G.piece_count(g) : Nat}
  L.landing.go(g, move, L.pinv_after(setup, moves), enemy)

def L.empty.go(+g: G.Game, +m: G.Action, +hp: {L.pinv(g) == True{} : Bool}, +en: {G.enemy_at(g, G.to_of(m)) == False{} : Bool}) -> {G.piece_count(G.apply(g, m)) == G.piece_count(g) : Nat}:
  match g m:
    case G.Game{turn, ps, b, r, tb, q, hst, res} G.Action{c, f, to}:
      +cp = G.Pieces.capture(ps, to, G.Side.other(turn))
      %Equal.sym(Nat, G.Pieces.len(G.Pieces.move(cp, f, to)), G.Pieces.len(cp), L.len_move(cp, f, to)) : {_ == G.Pieces.len(ps) : Nat}
      L.cap_keep(ps, to, G.Side.other(turn), hp, en)

def Laws.empty_square_keeps_pieces(setup, moves, move, legal, empty):
  +g = G.after(setup, moves)
  %Equal.sym(Bool, G.is_legal(g, move), True{}, legal) : {G.piece_count(G.play.go(_, g, move)) == G.piece_count(g) : Nat}
  L.empty.go(g, move, L.pinv_after(setup, moves), empty)

# ================================================================ group: a tap plays only legal moves

def L.pok(+g: G.Game, +me: G.Side, m: G.Action) -> Bool:
  G.click_ok.of(G.Click.play(m), g, me)

def L.aok(+g: G.Game, +me: G.Side, xs: List<&2, G.Action>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{m, t}:
      Bool.and(L.pok(g, me, m), L.aok(g, me, t))

def L.keep_ok(+g: G.Game, +me: G.Side, +b: Bool, +m: G.Action, +rest: List<&2, G.Action>, +hm: {L.pok(g, me, m) == True{} : Bool}, +hr: {L.aok(g, me, rest) == True{} : Bool}) -> {L.aok(g, me, G.Actions.keep(b, m, rest)) == True{} : Bool}:
  match b:
    case True{}:
      L.and2(L.pok(g, me, m), L.aok(g, me, rest), hm, hr)
    case False{}:
      hr

def L.with_card_ok(+g: G.Game, +me: G.Side, +xs: List<&2, G.Action>, +c: U32, +h: {L.aok(g, me, xs) == True{} : Bool}) -> {L.aok(g, me, G.Actions.with_card(xs, c)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.keep_ok(g, me, U32.is_eq(G.Action.card(m), c), m, G.Actions.with_card(t, c), L.and_l(L.pok(g, me, m), L.aok(g, me, t), h), L.with_card_ok(g, me, t, c, L.and_r(L.pok(g, me, m), L.aok(g, me, t), h)))

def L.with_to_ok(+g: G.Game, +me: G.Side, +xs: List<&2, G.Action>, +c: G.Cell, +h: {L.aok(g, me, xs) == True{} : Bool}) -> {L.aok(g, me, G.Actions.with_to(xs, c)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.keep_ok(g, me, G.Cell.eq(G.to_of(m), c), m, G.Actions.with_to(t, c), L.and_l(L.pok(g, me, m), L.aok(g, me, t), h), L.with_to_ok(g, me, t, c, L.and_r(L.pok(g, me, m), L.aok(g, me, t), h)))

def L.with_from_ok(+g: G.Game, +me: G.Side, +xs: List<&2, G.Action>, +c: Maybe<&2, G.Cell>, +h: {L.aok(g, me, xs) == True{} : Bool}) -> {L.aok(g, me, G.Actions.with_from(xs, c)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.keep_ok(g, me, G.Cell.is(c, G.Action.from(m)), m, G.Actions.with_from(t, c), L.and_l(L.pok(g, me, m), L.aok(g, me, t), h), L.with_from_ok(g, me, t, c, L.and_r(L.pok(g, me, m), L.aok(g, me, t), h)))

# ---- every legal move is a fine tap for the player to move

def L.ain(xs: List<&2, G.Action>, +ys: List<&2, G.Action>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{m, t}:
      Bool.and(G.Actions.has(ys, m), L.ain(t, ys))

def L.action_refl(+m: G.Action) -> {G.Action.same(m, m) == True{} : Bool}:
  match m:
    case G.Action{c, f, t}:
      %Equal.sym(Bool, U32.is_eq(c, c), True{}, L.u32_eq_refl(c)) : {Bool.and(Bool.and(_, G.Cell.eq(f, f)), G.Cell.eq(t, t)) == True{} : Bool}
      %Equal.sym(Bool, G.Cell.eq(f, f), True{}, L.cell_refl(f)) : {Bool.and(Bool.and(True{}, _), G.Cell.eq(t, t)) == True{} : Bool}
      L.cell_refl(t)

def L.ain_weaken(+xs: List<&2, G.Action>, +h: G.Action, +ys: List<&2, G.Action>, +a: {L.ain(xs, ys) == True{} : Bool}) -> {L.ain(xs, Con{h, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.and2(G.Actions.has(Con{h, ys}, m), L.ain(t, Con{h, ys}), L.or_r(G.Action.same(h, m), G.Actions.has(ys, m), L.and_l(G.Actions.has(ys, m), L.ain(t, ys), a)), L.ain_weaken(t, h, ys, L.and_r(G.Actions.has(ys, m), L.ain(t, ys), a)))

def L.ain_refl(+xs: List<&2, G.Action>) -> {L.ain(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.and2(G.Actions.has(Con{m, t}, m), L.ain(t, Con{m, t}), L.or_l(G.Action.same(m, m), G.Actions.has(t, m), L.action_refl(m)), L.ain_weaken(t, m, t, L.ain_refl(t)))

def L.pok_legal(+g: G.Game, +me: G.Side, +m: G.Action, +hs: {G.Side.same(G.Game.turn(g), me) == True{} : Bool}, +hl: {G.Actions.has(G.legal_moves(g), m) == True{} : Bool}) -> {L.pok(g, me, m) == True{} : Bool}:
  match m:
    case G.Action{c, f, t}:
      %Equal.sym(Bool, G.Side.same(G.Game.turn(g), me), True{}, hs) : {Bool.and(_, G.is_legal(g, G.Action{c, G.Cell.or_corner(G.Cell.of_u32(G.Cell.u32(f))), G.Cell.or_corner(G.Cell.of_u32(G.Cell.u32(t)))})) == True{} : Bool}
      %Equal.sym(Maybe<&2, G.Cell>, G.Cell.of_u32(G.Cell.u32(f)), Some{f}, L.cell_roundtrip(f)) : {G.is_legal(g, G.Action{c, G.Cell.or_corner(_), G.Cell.or_corner(G.Cell.of_u32(G.Cell.u32(t)))}) == True{} : Bool}
      %Equal.sym(Maybe<&2, G.Cell>, G.Cell.of_u32(G.Cell.u32(t)), Some{t}, L.cell_roundtrip(t)) : {G.is_legal(g, G.Action{c, f, G.Cell.or_corner(_)}) == True{} : Bool}
      hl

def L.aok_legal(+g: G.Game, +me: G.Side, +xs: List<&2, G.Action>, +hs: {G.Side.same(G.Game.turn(g), me) == True{} : Bool}, +a: {L.ain(xs, G.legal_moves(g)) == True{} : Bool}) -> {L.aok(g, me, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, t}:
      L.and2(L.pok(g, me, m), L.aok(g, me, t), L.pok_legal(g, me, m, hs, L.and_l(G.Actions.has(G.legal_moves(g), m), L.ain(t, G.legal_moves(g)), a)), L.aok_legal(g, me, t, hs, L.and_r(G.Actions.has(G.legal_moves(g), m), L.ain(t, G.legal_moves(g)), a)))

def L.moves_ok(+g: G.Game, +me: G.Side, +b: Bool, +eb: {G.Side.same(G.Game.turn(g), me) == b : Bool}) -> {L.aok(g, me, G.click.moves(b, g)) == True{} : Bool}:
  match b:
    case True{}:
      L.aok_legal(g, me, G.legal_moves(g), eb, L.ain_refl(G.legal_moves(g)))
    case False{}:
      {==}

# ---- whatever the tap decides is fine

def L.sel_ok(+g: G.Game, +me: G.Side, +mine: Bool, +same: Bool, +sq: G.Cell) -> {G.click_ok.of(G.click.select(mine, same, sq), g, me) == True{} : Bool}:
  match mine same:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def L.crowd_ok(+g: G.Game, +me: G.Side, +mine: Bool, +sq: G.Cell) -> {G.click_ok.of(G.click.crowd(mine, sq), g, me) == True{} : Bool}:
  match mine:
    case True{}:
      {==}
    case False{}:
      {==}

def L.reach_ok(+g: G.Game, +me: G.Side, +reach: List<&2, G.Action>, +mine: Bool, +sq: G.Cell, +ar: {L.aok(g, me, reach) == True{} : Bool}) -> {G.click_ok.of(G.click.reach(reach, mine, sq), g, me) == True{} : Bool}:
  match reach:
    case Nil{}:
      L.sel_ok(g, me, mine, False{}, sq)
    case Con{m, Nil{}}:
      L.and_l(L.pok(g, me, m), True{}, ar)
    case Con{m, Con{m2, t}}:
      L.crowd_ok(g, me, mine, sq)

def L.go_ok(+g: G.Game, +me: G.Side, +hit: List<&2, G.Action>, +none: Bool, +reach: List<&2, G.Action>, +mine: Bool, +same: Bool, +sq: G.Cell, +ah: {L.aok(g, me, hit) == True{} : Bool}, +ar: {L.aok(g, me, reach) == True{} : Bool}) -> {G.click_ok.of(G.click.go(hit, none, reach, mine, same, sq), g, me) == True{} : Bool}:
  match hit none:
    case Con{m, t} _:
      L.and_l(L.pok(g, me, m), L.aok(g, me, t), ah)
    case Nil{} True{}:
      L.reach_ok(g, me, reach, mine, sq, ar)
    case Nil{} False{}:
      L.sel_ok(g, me, mine, same, sq)

def L.tap.go(+g: G.Game, +me: G.Side, +card: U32, +s: U32, +at: Maybe<&2, G.Cell>) -> {G.click_ok.of(G.click.api(at, g, me, card, s), g, me) == True{} : Bool}:
  match at:
    case None{}:
      {==}
    case Some{sq}:
      +sel = G.Cell.of_u32(s)
      +moves = G.Actions.with_card(G.click.moves(G.Side.same(G.Game.turn(g), me), g), card)
      +am = L.with_card_ok(g, me, G.click.moves(G.Side.same(G.Game.turn(g), me), g), card, L.moves_ok(g, me, G.Side.same(G.Game.turn(g), me), {==}))
      +reach = G.Actions.with_to(moves, sq)
      +ar = L.with_to_ok(g, me, moves, sq, am)
      +ah = L.with_from_ok(g, me, reach, sel, ar)
      L.go_ok(g, me, G.Actions.with_from(reach, sel), G.Cell.none(sel), reach, G.Pieces.side_at(G.Game.pieces(g), sq, me), G.Cell.is(sel, sq), sq, ah, ar)

def Laws.tap_only_plays_legal_moves(setup, moves, me, card, sel, sq):
  +q = sq
  L.tap.go(G.after(setup, moves), me, card, sel, G.Cell.of_u32(q))

# ================================================================ group: the draw

def L.hands_dealt(+starter: G.Side, +d: G.Deal, +side: G.Side) -> {G.own_cards(G.start_dealt(starter, d), side) == G.Deal.hand_of(d, side) : List<&2, U32>}:
  match d side:
    case G.Deal{b, r, t} G.Blue{}:
      {==}
    case G.Deal{b, r, t} G.Red{}:
      {==}

def Laws.starting_hands_come_from_deal(setup, side):
  L.hands_dealt(G.Setup.starter(setup), G.Setup.deal(setup), side)

def Laws.every_deal_is_valid(blue, red):
  L.deal_valid(blue, red)

# ---------------------------------------------------------------- neither player forces the deal

def L.rotate_add(+a: Nat, +b: Nat, +xs: List<&2, U32>) -> {G.U32s.rotate(Nat.add(a, b), xs) == G.U32s.rotate(b, G.U32s.rotate(a, xs)) : List<&2, U32>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      L.rotate_add(p, b, G.U32s.rot1(xs))

def L.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, L.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, b), Nat.add(b, p), L.add_comm(p, b)) : {1n+_ == Nat.add(b, 1n+p) : Nat}
      Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), L.add_succ(b, p))

def L.npick(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# Where `x` sits in `xs`.
def L.idx(xs: List<&2, U32>, +x: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      L.npick(U32.is_eq(h, x), 0n, 1n+L.idx(t, x))

def L.utail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def L.lt_succ(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 1n+0n) == True{} : Bool}, L.false_is_not_true(h))
    case 1n+ap 1n+bp:
      L.lt_succ(ap, bp, h)

def L.nth_snoc(+t: List<&2, U32>, +h: U32, +j: Nat, +hj: {Nat.is_lt(j, G.U32s.len(t)) == True{} : Bool}) -> {G.U32s.nth(G.U32s.append(t, [h]), j) == G.U32s.nth(t, j) : U32}:
  match t j:
    case Nil{} 0n:
      Empty.absurd({G.U32s.nth(G.U32s.append(Nil{}, [h]), 0n) == G.U32s.nth(Nil{}, 0n) : U32}, L.false_is_not_true(hj))
    case Nil{} 1n+q:
      Empty.absurd({G.U32s.nth(G.U32s.append(Nil{}, [h]), 1n+q) == G.U32s.nth(Nil{}, 1n+q) : U32}, L.false_is_not_true(hj))
    case Con{y, r} 0n:
      {==}
    case Con{y, r} 1n+q:
      L.nth_snoc(r, h, q, hj)

# Turning a list `i` times (i below its length) brings its i-th card to the top.
def L.rot_head(+i: Nat, +xs: List<&2, U32>, +hi: {Nat.is_lt(i, G.U32s.len(xs)) == True{} : Bool}) -> {G.U32s.rotate(i, xs) == Con{G.U32s.nth(xs, i), L.utail(G.U32s.rotate(i, xs))} : List<&2, U32>}:
  match i xs:
    case _ Nil{}:
      Empty.absurd({G.U32s.rotate(i, Nil{}) == Con{G.U32s.nth(Nil{}, i), L.utail(G.U32s.rotate(i, Nil{}))} : List<&2, U32>}, L.false_is_not_true(hi))
    case 0n Con{h, t}:
      {==}
    case 1n+j Con{h, t}:
      +s = G.U32s.append(t, [h])
      +hj = {%Equal.sym(Nat, G.U32s.len(s), 1n+G.U32s.len(t), L.len_snoc(t, h)) : {Nat.is_lt(j, _) == True{} : Bool}; L.lt_succ(j, G.U32s.len(t), hi) : {Nat.is_lt(j, G.U32s.len(s)) == True{} : Bool}}
      %L.nth_snoc(t, h, j, hi) : {G.U32s.rotate(j, s) == Con{_, L.utail(G.U32s.rotate(j, s))} : List<&2, U32>}
      L.rot_head(j, s, hj)

def L.idx_ok.go(+h: U32, +t: List<&2, U32>, +x: U32, +b: Bool, +eb: {U32.is_eq(h, x) == b : Bool}, +m: {G.U32s.has(Con{h, t}, x) == True{} : Bool}, ih: {G.U32s.has(t, x) == True{} : Bool} -> {Bool.and(Nat.is_lt(L.idx(t, x), G.U32s.len(t)), U32.is_eq(G.U32s.nth(t, L.idx(t, x)), x)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(L.idx(Con{h, t}, x), G.U32s.len(Con{h, t})), U32.is_eq(G.U32s.nth(Con{h, t}, L.idx(Con{h, t}, x)), x)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(h, x), True{}, eb) : {Bool.and(Nat.is_lt(L.npick(_, 0n, 1n+L.idx(t, x)), 1n+G.U32s.len(t)), U32.is_eq(G.U32s.nth(Con{h, t}, L.npick(_, 0n, 1n+L.idx(t, x))), x)) == True{} : Bool}
      eb
    case False{}:
      %Equal.sym(Bool, U32.is_eq(h, x), False{}, eb) : {Bool.and(Nat.is_lt(L.npick(_, 0n, 1n+L.idx(t, x)), 1n+G.U32s.len(t)), U32.is_eq(G.U32s.nth(Con{h, t}, L.npick(_, 0n, 1n+L.idx(t, x))), x)) == True{} : Bool}
      ih({%eb : {Bool.or(_, G.U32s.has(t, x)) == True{} : Bool}; m : {G.U32s.has(t, x) == True{} : Bool}})

# A member's index is below the length and points at it.
def L.idx_ok(+xs: List<&2, U32>, +x: U32, +m: {G.U32s.has(xs, x) == True{} : Bool}) -> {Bool.and(Nat.is_lt(L.idx(xs, x), G.U32s.len(xs)), U32.is_eq(G.U32s.nth(xs, L.idx(xs, x)), x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Bool.and(Nat.is_lt(0n, 0n), U32.is_eq(99, x)) == True{} : Bool}, L.false_is_not_true(m))
    case Con{h, t}:
      L.idx_ok.go(h, t, x, U32.is_eq(h, x), {==}, m, m2 => L.idx_ok(t, x, m2))

# Turning to a member's index puts it on top.
def L.to_top(+xs: List<&2, U32>, +x: U32, +m: {G.U32s.has(xs, x) == True{} : Bool}) -> {G.U32s.rotate(L.idx(xs, x), xs) == Con{x, L.utail(G.U32s.rotate(L.idx(xs, x), xs))} : List<&2, U32>}:
  +ok = L.idx_ok(xs, x, m)
  +i = L.idx(xs, x)
  +lt = L.and_l(Nat.is_lt(i, G.U32s.len(xs)), U32.is_eq(G.U32s.nth(xs, i), x), ok)
  +nx = L.u32_eq_true(G.U32s.nth(xs, i), x, L.and_r(Nat.is_lt(i, G.U32s.len(xs)), U32.is_eq(G.U32s.nth(xs, i), x), ok))
  %nx : {G.U32s.rotate(i, xs) == Con{_, L.utail(G.U32s.rotate(i, xs))} : List<&2, U32>}
  L.rot_head(i, xs, lt)

def L.in_rot(+xs: List<&2, U32>, +k: Nat, +ys: List<&2, U32>) -> {G.U32s.all_in(xs, G.U32s.rotate(k, ys)) == G.U32s.all_in(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      %Equal.sym(Bool, G.U32s.has(G.U32s.rotate(k, ys), y), G.U32s.has(ys, y), L.rot_has(k, ys, y)) : {Bool.and(_, G.U32s.all_in(t, G.U32s.rotate(k, ys))) == Bool.and(G.U32s.has(ys, y), G.U32s.all_in(t, ys)) : Bool}
      %Equal.sym(Bool, G.U32s.all_in(t, G.U32s.rotate(k, ys)), G.U32s.all_in(t, ys), L.in_rot(t, k, ys)) : {Bool.and(G.U32s.has(ys, y), _) == Bool.and(G.U32s.has(ys, y), G.U32s.all_in(t, ys)) : Bool}
      {==}

def L.in_tail.go(+y: U32, +t: List<&2, U32>, +x: U32, +R: List<&2, U32>, +b: Bool, +eb: {U32.is_eq(x, y) == b : Bool}, +hx: {Bool.or(U32.is_eq(y, x), G.U32s.has(t, x)) == False{} : Bool}, +hy: {Bool.or(U32.is_eq(x, y), G.U32s.has(R, y)) == True{} : Bool}) -> {G.U32s.has(R, y) == True{} : Bool}:
  match b:
    case False{}:
      {%eb : {Bool.or(_, G.U32s.has(R, y)) == True{} : Bool}; hy : {G.U32s.has(R, y) == True{} : Bool}}
    case True{}:
      +yx = Equal.trans(Bool, U32.is_eq(y, x), U32.is_eq(x, y), True{}, L.u32_eq_sym(y, x), eb)
      Empty.absurd({G.U32s.has(R, y) == True{} : Bool}, L.true_is_not_false(Equal.trans(Bool, True{}, U32.is_eq(y, x), False{}, Equal.sym(Bool, U32.is_eq(y, x), True{}, yx), L.or_false_l(U32.is_eq(y, x), G.U32s.has(t, x), hx))))

# Members other than the top card are in the rest.
def L.in_tail(+xs: List<&2, U32>, +x: U32, +R: List<&2, U32>, +hx: {G.U32s.has(xs, x) == False{} : Bool}, +ha: {G.U32s.all_in(xs, Con{x, R}) == True{} : Bool}) -> {G.U32s.all_in(xs, R) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, t}:
      +hy = L.and_l(G.U32s.has(Con{x, R}, y), G.U32s.all_in(t, Con{x, R}), ha)
      L.and2(G.U32s.has(R, y), G.U32s.all_in(t, R), L.in_tail.go(y, t, x, R, U32.is_eq(x, y), {==}, hx, hy), L.in_tail(t, x, R, L.or_false_r(U32.is_eq(y, x), G.U32s.has(t, x), hx), L.and_r(G.U32s.has(Con{x, R}, y), G.U32s.all_in(t, Con{x, R}), ha)))

def L.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def L.red_for(ts: List<&2, U32>, +bs: List<&2, Nat>, +rem: List<&2, U32>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      +f0 = G.Nats.head0(bs)
      +k0 = L.idx(G.U32s.rotate(f0, rem), x)
      k0 <> L.red_for(xs, G.Nats.tail(bs), L.utail(G.U32s.rotate(k0, G.U32s.rotate(f0, rem))))

def L.force_red(+n: Nat, +ts: List<&2, U32>, +bs: List<&2, Nat>, +rem: List<&2, U32>, +hl: {G.U32s.len(ts) == n : Nat}, +hd: {G.U32s.distinct(ts) == True{} : Bool}, +ha: {G.U32s.all_in(ts, rem) == True{} : Bool}, +hr: {G.U32s.distinct(rem) == True{} : Bool}) -> {G.Draw.go(n, G.U32s.rotate(G.Draw.k(bs, L.red_for(ts, bs, rem)), rem), bs, L.red_for(ts, bs, rem)) == ts : List<&2, U32>}:
  match n ts:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xs}:
      Empty.absurd({G.Draw.go(0n, G.U32s.rotate(G.Draw.k(bs, L.red_for(Con{x, xs}, bs, rem)), rem), bs, L.red_for(Con{x, xs}, bs, rem)) == Con{x, xs} : List<&2, U32>}, L.nat_ne(1n+G.U32s.len(xs), 0n, hl, {==}))
    case 1n+p Nil{}:
      Empty.absurd({G.Draw.go(1n+p, G.U32s.rotate(G.Draw.k(bs, L.red_for(Nil{}, bs, rem)), rem), bs, L.red_for(Nil{}, bs, rem)) == Nil{} : List<&2, U32>}, L.nat_ne(0n, 1n+p, hl, {==}))
    case 1n+p Con{x, xs}:
      +f0 = G.Nats.head0(bs)
      +L0 = G.U32s.rotate(f0, rem)
      +k0 = L.idx(L0, x)
      +R = L.utail(G.U32s.rotate(k0, L0))
      +RF = L.red_for(Con{x, xs}, bs, rem)
      +hxr = L.and_l(G.U32s.has(rem, x), G.U32s.all_in(xs, rem), ha)
      +hxm = Equal.trans(Bool, G.U32s.has(L0, x), G.U32s.has(rem, x), True{}, L.rot_has(f0, rem, x), hxr)
      +top = L.to_top(L0, x, hxm)
      %Equal.sym(List<&2, U32>, G.U32s.rotate(Nat.add(f0, k0), rem), G.U32s.rotate(k0, L0), L.rotate_add(f0, k0, rem)) : {G.Draw.go(1n+p, _, bs, RF) == Con{x, xs} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, G.U32s.rotate(k0, L0), Con{x, R}, top) : {G.Draw.go(1n+p, _, bs, RF) == Con{x, xs} : List<&2, U32>}
      +hl2 = Equal.cong(Nat, Nat, z => L.pred(z), 1n+G.U32s.len(xs), 1n+p, hl)
      +hd2 = L.and_r(Bool.not(G.U32s.has(xs, x)), G.U32s.distinct(xs), hd)
      +nx = L.not_true(G.U32s.has(xs, x), L.and_l(Bool.not(G.U32s.has(xs, x)), G.U32s.distinct(xs), hd))
      +a1 = Equal.trans(Bool, G.U32s.all_in(xs, L0), G.U32s.all_in(xs, rem), True{}, L.in_rot(xs, f0, rem), L.and_r(G.U32s.has(rem, x), G.U32s.all_in(xs, rem), ha))
      +a2 = Equal.trans(Bool, G.U32s.all_in(xs, G.U32s.rotate(k0, L0)), G.U32s.all_in(xs, L0), True{}, L.in_rot(xs, k0, L0), a1)
      +a3 = {%top : {G.U32s.all_in(xs, _) == True{} : Bool}; a2 : {G.U32s.all_in(xs, Con{x, R}) == True{} : Bool}}
      +d1 = Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(k0, L0)), G.U32s.distinct(rem), True{}, Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(k0, L0)), G.U32s.distinct(L0), G.U32s.distinct(rem), L.rot_dist(k0, L0), L.rot_dist(f0, rem)), hr)
      +d2 = {%top : {G.U32s.distinct(_) == True{} : Bool}; d1 : {G.U32s.distinct(Con{x, R}) == True{} : Bool}}
      +ih = L.force_red(p, xs, G.Nats.tail(bs), R, hl2, hd2, L.in_tail(xs, x, R, nx, a3), L.and_r(Bool.not(G.U32s.has(R, x)), G.U32s.distinct(R), d2))
      %Equal.sym(List<&2, U32>, G.Draw.go(p, G.U32s.rotate(G.Draw.k(G.Nats.tail(bs), L.red_for(xs, G.Nats.tail(bs), R)), R), G.Nats.tail(bs), L.red_for(xs, G.Nats.tail(bs), R)), xs, ih) : {Con{x, _} == Con{x, xs} : List<&2, U32>}
      {==}

def L.blue_for(ts: List<&2, U32>, +rs: List<&2, Nat>, +rem: List<&2, U32>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      +f0 = G.Nats.head0(rs)
      +k0 = L.idx(G.U32s.rotate(f0, rem), x)
      k0 <> L.blue_for(xs, G.Nats.tail(rs), L.utail(G.U32s.rotate(k0, G.U32s.rotate(f0, rem))))

def L.force_blue(+n: Nat, +ts: List<&2, U32>, +rs: List<&2, Nat>, +rem: List<&2, U32>, +hl: {G.U32s.len(ts) == n : Nat}, +hd: {G.U32s.distinct(ts) == True{} : Bool}, +ha: {G.U32s.all_in(ts, rem) == True{} : Bool}, +hr: {G.U32s.distinct(rem) == True{} : Bool}) -> {G.Draw.go(n, G.U32s.rotate(G.Draw.k(L.blue_for(ts, rs, rem), rs), rem), L.blue_for(ts, rs, rem), rs) == ts : List<&2, U32>}:
  match n ts:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xs}:
      Empty.absurd({G.Draw.go(0n, G.U32s.rotate(G.Draw.k(L.blue_for(Con{x, xs}, rs, rem), rs), rem), L.blue_for(Con{x, xs}, rs, rem), rs) == Con{x, xs} : List<&2, U32>}, L.nat_ne(1n+G.U32s.len(xs), 0n, hl, {==}))
    case 1n+p Nil{}:
      Empty.absurd({G.Draw.go(1n+p, G.U32s.rotate(G.Draw.k(L.blue_for(Nil{}, rs, rem), rs), rem), L.blue_for(Nil{}, rs, rem), rs) == Nil{} : List<&2, U32>}, L.nat_ne(0n, 1n+p, hl, {==}))
    case 1n+p Con{x, xs}:
      +f0 = G.Nats.head0(rs)
      +L0 = G.U32s.rotate(f0, rem)
      +k0 = L.idx(L0, x)
      +R = L.utail(G.U32s.rotate(k0, L0))
      +RF = L.blue_for(Con{x, xs}, rs, rem)
      +hxr = L.and_l(G.U32s.has(rem, x), G.U32s.all_in(xs, rem), ha)
      +hxm = Equal.trans(Bool, G.U32s.has(L0, x), G.U32s.has(rem, x), True{}, L.rot_has(f0, rem, x), hxr)
      +top = L.to_top(L0, x, hxm)
      %L.add_comm(f0, k0) : {G.Draw.go(1n+p, G.U32s.rotate(_, rem), RF, rs) == Con{x, xs} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, G.U32s.rotate(Nat.add(f0, k0), rem), G.U32s.rotate(k0, L0), L.rotate_add(f0, k0, rem)) : {G.Draw.go(1n+p, _, RF, rs) == Con{x, xs} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, G.U32s.rotate(k0, L0), Con{x, R}, top) : {G.Draw.go(1n+p, _, RF, rs) == Con{x, xs} : List<&2, U32>}
      +hl2 = Equal.cong(Nat, Nat, z => L.pred(z), 1n+G.U32s.len(xs), 1n+p, hl)
      +hd2 = L.and_r(Bool.not(G.U32s.has(xs, x)), G.U32s.distinct(xs), hd)
      +nx = L.not_true(G.U32s.has(xs, x), L.and_l(Bool.not(G.U32s.has(xs, x)), G.U32s.distinct(xs), hd))
      +a1 = Equal.trans(Bool, G.U32s.all_in(xs, L0), G.U32s.all_in(xs, rem), True{}, L.in_rot(xs, f0, rem), L.and_r(G.U32s.has(rem, x), G.U32s.all_in(xs, rem), ha))
      +a2 = Equal.trans(Bool, G.U32s.all_in(xs, G.U32s.rotate(k0, L0)), G.U32s.all_in(xs, L0), True{}, L.in_rot(xs, k0, L0), a1)
      +a3 = {%top : {G.U32s.all_in(xs, _) == True{} : Bool}; a2 : {G.U32s.all_in(xs, Con{x, R}) == True{} : Bool}}
      +d1 = Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(k0, L0)), G.U32s.distinct(rem), True{}, Equal.trans(Bool, G.U32s.distinct(G.U32s.rotate(k0, L0)), G.U32s.distinct(L0), G.U32s.distinct(rem), L.rot_dist(k0, L0), L.rot_dist(f0, rem)), hr)
      +d2 = {%top : {G.U32s.distinct(_) == True{} : Bool}; d1 : {G.U32s.distinct(Con{x, R}) == True{} : Bool}}
      +ih = L.force_blue(p, xs, G.Nats.tail(rs), R, hl2, hd2, L.in_tail(xs, x, R, nx, a3), L.and_r(Bool.not(G.U32s.has(R, x)), G.U32s.distinct(R), d2))
      %Equal.sym(List<&2, U32>, G.Draw.go(p, G.U32s.rotate(G.Draw.k(L.blue_for(xs, G.Nats.tail(rs), R), G.Nats.tail(rs)), R), L.blue_for(xs, G.Nats.tail(rs), R), G.Nats.tail(rs)), xs, ih) : {Con{x, _} == Con{x, xs} : List<&2, U32>}
      {==}

def L.red_deal(+bc: Bool, +bs: List<&2, Nat>, +a: U32, +b: U32, +c: U32, +e: U32, +t: U32, +hv: {G.Deal.five_ok([a, b, c, e, t]) == True{} : Bool}) -> {G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, L.red_for([a, b, c, e, t], bs, G.Cards.ids(G.deck()))}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Nil{}}}, t} : G.Deal}:
  +rs = L.red_for([a, b, c, e, t], bs, G.Cards.ids(G.deck()))
  +f = L.force_red(5n, [a, b, c, e, t], bs, G.Cards.ids(G.deck()), {==}, L.and_l(G.U32s.distinct([a, b, c, e, t]), G.U32s.all_in([a, b, c, e, t], G.Cards.ids(G.deck())), hv), L.and_r(G.U32s.distinct([a, b, c, e, t]), G.U32s.all_in([a, b, c, e, t], G.Cards.ids(G.deck())), hv), {==})
  %Equal.sym(List<&2, U32>, G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs), [a, b, c, e, t], f) : {G.Deal.of_list(_) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Nil{}}}, t} : G.Deal}
  {==}

def L.blue_deal(+rc: Bool, +rs: List<&2, Nat>, +a: U32, +b: U32, +c: U32, +e: U32, +t: U32, +hv: {G.Deal.five_ok([a, b, c, e, t]) == True{} : Bool}) -> {G.deal_from(G.Secret{False{}, L.blue_for([a, b, c, e, t], rs, G.Cards.ids(G.deck()))}, G.Secret{rc, rs}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Nil{}}}, t} : G.Deal}:
  +bs = L.blue_for([a, b, c, e, t], rs, G.Cards.ids(G.deck()))
  +f = L.force_blue(5n, [a, b, c, e, t], rs, G.Cards.ids(G.deck()), {==}, L.and_l(G.U32s.distinct([a, b, c, e, t]), G.U32s.all_in([a, b, c, e, t], G.Cards.ids(G.deck())), hv), L.and_r(G.U32s.distinct([a, b, c, e, t]), G.U32s.all_in([a, b, c, e, t], G.Cards.ids(G.deck())), hv), {==})
  %Equal.sym(List<&2, U32>, G.Draw.go(5n, G.U32s.rotate(G.Draw.k(bs, rs), G.Cards.ids(G.deck())), bs, rs), [a, b, c, e, t], f) : {G.Deal.of_list(_) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Nil{}}}, t} : G.Deal}
  {==}

# Blue cannot force the deal: for any blue secret and any valid deal, red has a secret that makes it.
def Laws.blue_cannot_force_the_deal(blue, deal, valid):
  match blue deal:
    case G.Secret{+bc, +bs} G.Deal{Con{+a, Con{+b, Nil{}}}, Con{+c, Con{+e, Nil{}}}, +t}:
      (G.Secret{False{}, L.red_for([a, b, c, e, t], bs, G.Cards.ids(G.deck()))}, L.red_deal(bc, bs, a, b, c, e, t, valid))
    case G.Secret{+bc, +bs} G.Deal{Nil{}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Nil{}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+bc, +bs} G.Deal{Con{a, Nil{}}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Con{a, Nil{}}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+bc, +bs} G.Deal{Con{a, Con{b, Con{x, y}}}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Con{a, Con{b, Con{x, y}}}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+bc, +bs} G.Deal{Con{a, Con{b, Nil{}}}, Nil{}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Con{a, Con{b, Nil{}}}, Nil{}, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+bc, +bs} G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Nil{}}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Nil{}}, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+bc, +bs} G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Con{x, y}}}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{bc, bs}, G.Secret{False{}, Nil{}}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Con{x, y}}}, t} : G.Deal}, L.false_is_not_true(valid)))

# Nor can red: for any red secret and any valid deal, blue has a secret that makes it.
def Laws.red_cannot_force_the_deal(red, deal, valid):
  match red deal:
    case G.Secret{+rc, +rs} G.Deal{Con{+a, Con{+b, Nil{}}}, Con{+c, Con{+e, Nil{}}}, +t}:
      (G.Secret{False{}, L.blue_for([a, b, c, e, t], rs, G.Cards.ids(G.deck()))}, L.blue_deal(rc, rs, a, b, c, e, t, valid))
    case G.Secret{+rc, +rs} G.Deal{Nil{}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Nil{}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+rc, +rs} G.Deal{Con{a, Nil{}}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Con{a, Nil{}}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+rc, +rs} G.Deal{Con{a, Con{b, Con{x, y}}}, r, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Con{a, Con{b, Con{x, y}}}, r, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+rc, +rs} G.Deal{Con{a, Con{b, Nil{}}}, Nil{}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Con{a, Con{b, Nil{}}}, Nil{}, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+rc, +rs} G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Nil{}}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Nil{}}, t} : G.Deal}, L.false_is_not_true(valid)))
    case G.Secret{+rc, +rs} G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Con{x, y}}}, t}:
      (G.Secret{False{}, Nil{}}, Empty.absurd({G.deal_from(G.Secret{False{}, Nil{}}, G.Secret{rc, rs}) == G.Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Con{x, y}}}, t} : G.Deal}, L.false_is_not_true(valid)))

# ================================================================ group: what the table draws

def L.seven(+starter: G.Side, +d: G.Deal, +side: G.Side) -> {G.Tokens.count(G.scene(G.start_dealt(starter, d)), side) == 7n : Nat}:
  match d side:
    case G.Deal{b, r, t} G.Blue{}:
      {==}
    case G.Deal{b, r, t} G.Red{}:
      {==}

def Laws.starts_with_seven_each(setup, side):
  L.seven(G.Setup.starter(setup), G.Setup.deal(setup), side)

def L.scene_code(+ps: List<&2, G.Piece>, +sq: G.Cell) -> {G.Tokens.code_at(G.scene.of(ps), sq) == G.Pieces.code_at(ps, sq) : U32}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      %Equal.sym(U32, G.Tokens.code_at(G.scene.of(rest), sq), G.Pieces.code_at(rest, sq), L.scene_code(rest, sq)) : {G.sel(G.Cell.eq(q, sq), G.Piece.code(s, t), _) == G.sel(G.Cell.eq(q, sq), G.Piece.code(s, t), G.Pieces.code_at(rest, sq)) : U32}
      {==}

def Laws.table_shows_the_board(setup, moves, sq):
  L.scene_code(G.Game.pieces(G.after(setup, moves)), sq)

def L.scene_len(+ps: List<&2, G.Piece>) -> {G.Tokens.len(G.scene.of(ps)) == G.Pieces.len(ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      %Equal.sym(Nat, G.Tokens.len(G.scene.of(rest)), G.Pieces.len(rest), L.scene_len(rest)) : {1n+_ == 1n+G.Pieces.len(rest) : Nat}
      {==}

def Laws.one_token_per_piece(setup, moves):
  L.scene_len(G.Game.pieces(G.after(setup, moves)))

def L.scene_cells(+ps: List<&2, G.Piece>) -> {G.Tokens.cells(G.scene.of(ps)) == L.cells(ps) : List<&2, G.Cell>}:
  match ps:
    case Nil{}:
      {==}
    case Con{G.Piece{s, t, q}, rest}:
      %Equal.sym(List<&2, G.Cell>, G.Tokens.cells(G.scene.of(rest)), L.cells(rest), L.scene_cells(rest)) : {q <> _ == q <> L.cells(rest) : List<&2, G.Cell>}
      {==}

def L.unstacked_is_distinct(+xs: List<&2, G.Cell>) -> {G.Cells.unstacked(xs) == L.distinct(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, G.Cells.unstacked(t), L.distinct(t), L.unstacked_is_distinct(t)) : {Bool.and(Bool.not(G.Cells.has(t, h)), _) == Bool.and(Bool.not(G.Cells.has(t, h)), L.distinct(t)) : Bool}
      {==}

def Laws.tokens_never_stack(setup, moves):
  +ps = G.Game.pieces(G.after(setup, moves))
  %Equal.sym(List<&2, G.Cell>, G.Tokens.cells(G.scene.of(ps)), L.cells(ps), L.scene_cells(ps)) : {G.Cells.unstacked(_) == True{} : Bool}
  Equal.trans(Bool, G.Cells.unstacked(L.cells(ps)), L.distinct(L.cells(ps)), True{}, L.unstacked_is_distinct(L.cells(ps)), L.pinv_after(setup, moves))

# ================================================================ group: the online protocol

def L.keys_blue(+p0: Nat) -> {Bool.and(G.Nats.has(G.Proto.handed(True{}), p0), G.Nats.has(G.Proto.mine(True{}), p0)) == False{} : Bool}:
  match p0:
    case 0n:
      {==}
    case 1n+p1:
      match p1:
        case 0n:
          {==}
        case 1n+p2:
          match p2:
            case 0n:
              {==}
            case 1n+p3:
              match p3:
                case 0n:
                  {==}
                case 1n+p4:
                  match p4:
                    case 0n:
                      {==}
                    case 1n+p5:
                      {==}

def L.keys_red(+p0: Nat) -> {Bool.and(G.Nats.has(G.Proto.handed(False{}), p0), G.Nats.has(G.Proto.mine(False{}), p0)) == False{} : Bool}:
  match p0:
    case 0n:
      {==}
    case 1n+p1:
      match p1:
        case 0n:
          {==}
        case 1n+p2:
          match p2:
            case 0n:
              {==}
            case 1n+p3:
              match p3:
                case 0n:
                  {==}
                case 1n+p4:
                  match p4:
                    case 0n:
                      {==}
                    case 1n+p5:
                      {==}

def Laws.keys_never_open_my_cards(host, pos):
  match host:
    case True{}:
      L.keys_blue(pos)
    case False{}:
      L.keys_red(pos)

def L.hands_apart(+p0: Nat) -> {Bool.and(G.Nats.has(G.Proto.mine(True{}), p0), G.Nats.has(G.Proto.mine(False{}), p0)) == False{} : Bool}:
  match p0:
    case 0n:
      {==}
    case 1n+p1:
      match p1:
        case 0n:
          {==}
        case 1n+p2:
          match p2:
            case 0n:
              {==}
            case 1n+p3:
              match p3:
                case 0n:
                  {==}
                case 1n+p4:
                  match p4:
                    case 0n:
                      {==}
                    case 1n+p5:
                      {==}

def Laws.hands_never_share_a_position(pos):
  L.hands_apart(pos)

def L.noproof.go(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +b: Bool, +eb: {G.U32s.has(seen, c) == b : Bool}, +acc: {G.Verdict.ok(G.Opp.play.go(G.U32s.has(seen, c), hid, seen, tb, c, G.NoProof{})) == True{} : Bool}) -> {G.U32s.has(seen, c) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({G.U32s.has(seen, c) == True{} : Bool}, L.false_is_not_true({%eb : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.NoProof{})) == True{} : Bool}; acc : {False{} == True{} : Bool}}))

def Laws.no_proof_only_seen_cards(opp, card, accepted):
  match opp:
    case G.Opp{hid, seen, tb}:
      L.noproof.go(hid, seen, tb, card, G.U32s.has(seen, card), {==}, accepted)

def L.opens.go(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +pos: Nat, +opened: U32, +k: Bool, +ek: {Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)) == k : Bool}, +acc: {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}) -> {Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)) == True{} : Bool}:
  match k:
    case True{}:
      ek
    case False{}:
      Empty.absurd({Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)) == True{} : Bool}, L.false_is_not_true({%ek : {G.Verdict.ok(G.Opp.check(_, pos, hid, seen, tb, c)) == True{} : Bool}; acc : {False{} == True{} : Bool}}))

def Laws.proof_must_open_that_card(opp, card, pos, opened, unseen, accepted):
  match opp:
    case G.Opp{hid, seen, tb}:
      +c = card
      +acc = {%unseen : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, opened})) == True{} : Bool}; accepted : {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}}
      L.opens.go(hid, seen, tb, c, pos, opened, Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), {==}, acc)

def L.honest.go(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +pos: Nat, +b: Bool, +eb: {G.U32s.has(seen, c) == b : Bool}, +hidden: {G.Nats.has(hid, pos) == True{} : Bool}) -> {G.Verdict.ok(G.Opp.play.go(G.U32s.has(seen, c), hid, seen, tb, c, G.Opened{pos, c})) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, G.U32s.has(seen, c), True{}, eb) : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, c})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, G.U32s.has(seen, c), False{}, eb) : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, c})) == True{} : Bool}
      %Equal.sym(Bool, G.Nats.has(hid, pos), True{}, hidden) : {G.Verdict.ok(G.Opp.check(Bool.and(_, U32.is_eq(c, c)), pos, hid, seen, tb, c)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(c, c), True{}, L.u32_eq_refl(c)) : {G.Verdict.ok(G.Opp.check(Bool.and(True{}, _), pos, hid, seen, tb, c)) == True{} : Bool}
      {==}

def Laws.honest_card_accepted(opp, card, pos, hidden):
  match opp:
    case G.Opp{hid, seen, tb}:
      L.honest.go(hid, seen, tb, card, pos, G.U32s.has(seen, card), {==}, hidden)

def L.without.go(+h: Nat, +t: List<&2, Nat>, +x: Nat, +b: Bool, +eb: {Nat.is_eq(h, x) == b : Bool}, +ih: {G.Nats.has(G.Nats.without(t, x), x) == False{} : Bool}) -> {G.Nats.has(G.Nats.keep(Nat.is_eq(h, x), h, G.Nats.without(t, x)), x) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(h, x), True{}, eb) : {G.Nats.has(G.Nats.keep(_, h, G.Nats.without(t, x)), x) == False{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(h, x), False{}, eb) : {G.Nats.has(G.Nats.keep(_, h, G.Nats.without(t, x)), x) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(h, x), False{}, eb) : {Bool.or(_, G.Nats.has(G.Nats.without(t, x), x)) == False{} : Bool}
      ih

def L.without_gone(+xs: List<&2, Nat>, +x: Nat) -> {G.Nats.has(G.Nats.without(xs, x), x) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      L.without.go(h, t, x, Nat.is_eq(h, x), {==}, L.without_gone(t, x))

def L.once.go(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +pos: Nat, +opened: U32, +k: Bool, +ek: {Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)) == k : Bool}, +acc: {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}) -> {G.Nats.has(G.Opp.hidden(G.Verdict.opp(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c), G.Opp{hid, seen, tb})), pos) == False{} : Bool}:
  match k:
    case True{}:
      %Equal.sym(Bool, Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), True{}, ek) : {G.Nats.has(G.Opp.hidden(G.Verdict.opp(G.Opp.check(_, pos, hid, seen, tb, c), G.Opp{hid, seen, tb})), pos) == False{} : Bool}
      L.without_gone(hid, pos)
    case False{}:
      Empty.absurd({G.Nats.has(G.Opp.hidden(G.Verdict.opp(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c), G.Opp{hid, seen, tb})), pos) == False{} : Bool}, L.false_is_not_true({%ek : {G.Verdict.ok(G.Opp.check(_, pos, hid, seen, tb, c)) == True{} : Bool}; acc : {False{} == True{} : Bool}}))

def Laws.each_position_proves_once(opp, card, pos, opened, unseen, accepted):
  match opp:
    case G.Opp{hid, seen, tb}:
      +c = card
      +un = {unseen : {G.U32s.has(seen, c) == False{} : Bool}}
      +acc = {%un : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, opened})) == True{} : Bool}; accepted : {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}}
      %Equal.sym(Bool, G.U32s.has(seen, c), False{}, un) : {G.Nats.has(G.Opp.hidden(G.Verdict.opp(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, opened}), G.Opp{hid, seen, tb})), pos) == False{} : Bool}
      L.once.go(hid, seen, tb, c, pos, opened, Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), {==}, acc)

def L.table.check(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +pos: Nat, +opened: U32, +k: Bool, +ek: {Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)) == k : Bool}, +acc: {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}) -> {G.Opp.table(G.Verdict.opp(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c), G.Opp{hid, seen, tb})) == c : U32}:
  match k:
    case True{}:
      %Equal.sym(Bool, Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), True{}, ek) : {G.Opp.table(G.Verdict.opp(G.Opp.check(_, pos, hid, seen, tb, c), G.Opp{hid, seen, tb})) == c : U32}
      {==}
    case False{}:
      Empty.absurd({G.Opp.table(G.Verdict.opp(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c), G.Opp{hid, seen, tb})) == c : U32}, L.false_is_not_true({%ek : {G.Verdict.ok(G.Opp.check(_, pos, hid, seen, tb, c)) == True{} : Bool}; acc : {False{} == True{} : Bool}}))

def L.table.go(+hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, +proof: G.Proof, +b: Bool, +eb: {G.U32s.has(seen, c) == b : Bool}, +acc: {G.Verdict.ok(G.Opp.play.go(G.U32s.has(seen, c), hid, seen, tb, c, proof)) == True{} : Bool}) -> {G.Opp.table(G.Verdict.opp(G.Opp.play.go(G.U32s.has(seen, c), hid, seen, tb, c, proof), G.Opp{hid, seen, tb})) == c : U32}:
  match proof b:
    case _ True{}:
      %Equal.sym(Bool, G.U32s.has(seen, c), True{}, eb) : {G.Opp.table(G.Verdict.opp(G.Opp.play.go(_, hid, seen, tb, c, proof), G.Opp{hid, seen, tb})) == c : U32}
      {==}
    case G.NoProof{} False{}:
      Empty.absurd({G.Opp.table(G.Verdict.opp(G.Opp.play.go(G.U32s.has(seen, c), hid, seen, tb, c, G.NoProof{}), G.Opp{hid, seen, tb})) == c : U32}, L.false_is_not_true({%eb : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.NoProof{})) == True{} : Bool}; acc : {False{} == True{} : Bool}}))
    case G.Opened{pos, opened} False{}:
      +a2 = {%eb : {G.Verdict.ok(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, opened})) == True{} : Bool}; acc : {G.Verdict.ok(G.Opp.check(Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), pos, hid, seen, tb, c)) == True{} : Bool}}
      %Equal.sym(Bool, G.U32s.has(seen, c), False{}, eb) : {G.Opp.table(G.Verdict.opp(G.Opp.play.go(_, hid, seen, tb, c, G.Opened{pos, opened}), G.Opp{hid, seen, tb})) == c : U32}
      L.table.check(hid, seen, tb, c, pos, opened, Bool.and(G.Nats.has(hid, pos), U32.is_eq(opened, c)), {==}, a2)

def Laws.accepted_card_goes_to_table(opp, card, proof, accepted):
  match opp:
    case G.Opp{hid, seen, tb}:
      L.table.go(hid, seen, tb, card, proof, G.U32s.has(seen, card), {==}, accepted)

def L.mine.go(+hc: U32, +p: Nat, +t: List<&2, G.Held>, +c: U32, +b: Bool, +eb: {U32.is_eq(hc, c) == b : Bool}, +ih: {G.Mine.pos(G.Mine.play(t, c), c) == 99n : Nat}) -> {G.Mine.pos(G.Mine.keep(U32.is_eq(hc, c), G.Held{hc, p}, G.Mine.play(t, c)), c) == 99n : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(hc, c), True{}, eb) : {G.Mine.pos(G.Mine.keep(_, G.Held{hc, p}, G.Mine.play(t, c)), c) == 99n : Nat}
      ih
    case False{}:
      %Equal.sym(Bool, U32.is_eq(hc, c), False{}, eb) : {G.Mine.pos(G.Mine.keep(_, G.Held{hc, p}, G.Mine.play(t, c)), c) == 99n : Nat}
      %Equal.sym(Bool, U32.is_eq(hc, c), False{}, eb) : {G.Mine.pos.pick(_, p, G.Mine.pos(G.Mine.play(t, c), c)) == 99n : Nat}
      ih

def Laws.my_key_goes_once(held, card):
  match held:
    case Nil{}:
      {==}
    case Con{G.Held{hc, p}, t}:
      L.mine.go(hc, p, t, card, U32.is_eq(hc, card), {==}, Laws.my_key_goes_once(t, card))

# ---- the order of the messages and the coin

def L.in_order_True(+step: Nat, +during: {Nat.is_lt(step, 5n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, step)) == G.Take{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      {==}
                    case 1n+step_0_1_2_3_4:
                      match step_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(True{}, 5n+step_0_1_2_3_4, G.Proto.expected(True{}, 5n+step_0_1_2_3_4)) == G.Take{} : G.Order}, L.false_is_not_true(during))
                        case 1n+step_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(True{}, 5n+step_0_1_2_3_4, G.Proto.expected(True{}, 5n+step_0_1_2_3_4)) == G.Take{} : G.Order}, L.false_is_not_true(during))

def L.no_move_True(+step: Nat, +during: {Nat.is_lt(step, 5n) == True{} : Bool}) -> {G.Proto.order(True{}, step, 8) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      {==}
                    case 1n+step_0_1_2_3_4:
                      match step_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(True{}, 5n+step_0_1_2_3_4, 8) == G.Cheat{} : G.Order}, L.false_is_not_true(during))
                        case 1n+step_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(True{}, 5n+step_0_1_2_3_4, 8) == G.Cheat{} : G.Order}, L.false_is_not_true(during))

def L.late_True_0(+step: Nat, +before: {Nat.is_lt(0n, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 0n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 0n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      {==}

def L.late_True_1(+step: Nat, +before: {Nat.is_lt(1n, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 1n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 1n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(True{}, 1n, G.Proto.expected(True{}, 1n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          {==}

def L.late_True_2(+step: Nat, +before: {Nat.is_lt(2n, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 2n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(True{}, 1n, G.Proto.expected(True{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(True{}, 2n, G.Proto.expected(True{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              {==}

def L.late_True_3(+step: Nat, +before: {Nat.is_lt(3n, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 3n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(True{}, 1n, G.Proto.expected(True{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(True{}, 2n, G.Proto.expected(True{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(True{}, 3n, G.Proto.expected(True{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                case 1n+step_0_1_2_3:
                  {==}

def L.late_True_4(+step: Nat, +before: {Nat.is_lt(4n, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(True{}, 1n, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(True{}, 2n, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(True{}, 3n, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      Empty.absurd({G.Proto.order(True{}, 4n, G.Proto.expected(True{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                    case 1n+step_0_1_2_3_4:
                      {==}

def L.late_True(+step: Nat, +earlier: Nat, +before: {Nat.is_lt(earlier, step) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, earlier)) == G.Cheat{} : G.Order}:
  match earlier:
    case 0n:
      L.late_True_0(step, before)
    case 1n+earlier_0:
      match earlier_0:
        case 0n:
          L.late_True_1(step, before)
        case 1n+earlier_0_1:
          match earlier_0_1:
            case 0n:
              L.late_True_2(step, before)
            case 1n+earlier_0_1_2:
              match earlier_0_1_2:
                case 0n:
                  L.late_True_3(step, before)
                case 1n+earlier_0_1_2_3:
                  match earlier_0_1_2_3:
                    case 0n:
                      L.late_True_4(step, before)
                    case 1n+earlier_0_1_2_3_4:
                      {==}

def L.early_True_0(+step: Nat, +after: {Nat.is_lt(step, 0n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 0n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(True{}, 0n, G.Proto.expected(True{}, 0n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
    case 1n+r:
      Empty.absurd({G.Proto.order(True{}, 1n+r, G.Proto.expected(True{}, 0n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_True_1(+step: Nat, +after: {Nat.is_lt(step, 1n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 1n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(True{}, 1n, G.Proto.expected(True{}, 1n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
        case 1n+step_0_x:
          Empty.absurd({G.Proto.order(True{}, 2n+step_0_x, G.Proto.expected(True{}, 1n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_True_2(+step: Nat, +after: {Nat.is_lt(step, 2n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 2n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(True{}, 2n, G.Proto.expected(True{}, 2n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
            case 1n+step_0_1_x:
              Empty.absurd({G.Proto.order(True{}, 3n+step_0_1_x, G.Proto.expected(True{}, 2n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_True_3(+step: Nat, +after: {Nat.is_lt(step, 3n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 3n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(True{}, 3n, G.Proto.expected(True{}, 3n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
                case 1n+step_0_1_2_x:
                  Empty.absurd({G.Proto.order(True{}, 4n+step_0_1_2_x, G.Proto.expected(True{}, 3n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_True_4(+step: Nat, +after: {Nat.is_lt(step, 4n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, 4n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      Empty.absurd({G.Proto.order(True{}, 4n, G.Proto.expected(True{}, 4n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
                    case 1n+step_0_1_2_3_x:
                      Empty.absurd({G.Proto.order(True{}, 5n+step_0_1_2_3_x, G.Proto.expected(True{}, 4n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_True(+step: Nat, +later: Nat, +after: {Nat.is_lt(step, later) == True{} : Bool}, +during: {Nat.is_lt(later, 5n) == True{} : Bool}) -> {G.Proto.order(True{}, step, G.Proto.expected(True{}, later)) == G.Hold{} : G.Order}:
  match later:
    case 0n:
      L.early_True_0(step, after)
    case 1n+later_0:
      match later_0:
        case 0n:
          L.early_True_1(step, after)
        case 1n+later_0_1:
          match later_0_1:
            case 0n:
              L.early_True_2(step, after)
            case 1n+later_0_1_2:
              match later_0_1_2:
                case 0n:
                  L.early_True_3(step, after)
                case 1n+later_0_1_2_3:
                  match later_0_1_2_3:
                    case 0n:
                      L.early_True_4(step, after)
                    case 1n+later_0_1_2_3_4:
                      match later_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(True{}, step, G.Proto.expected(True{}, 5n+later_0_1_2_3_4)) == G.Hold{} : G.Order}, L.false_is_not_true(during))
                        case 1n+later_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(True{}, step, G.Proto.expected(True{}, 5n+later_0_1_2_3_4)) == G.Hold{} : G.Order}, L.false_is_not_true(during))

def L.in_order_False(+step: Nat, +during: {Nat.is_lt(step, 5n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, step)) == G.Take{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      {==}
                    case 1n+step_0_1_2_3_4:
                      match step_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(False{}, 5n+step_0_1_2_3_4, G.Proto.expected(False{}, 5n+step_0_1_2_3_4)) == G.Take{} : G.Order}, L.false_is_not_true(during))
                        case 1n+step_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(False{}, 5n+step_0_1_2_3_4, G.Proto.expected(False{}, 5n+step_0_1_2_3_4)) == G.Take{} : G.Order}, L.false_is_not_true(during))

def L.no_move_False(+step: Nat, +during: {Nat.is_lt(step, 5n) == True{} : Bool}) -> {G.Proto.order(False{}, step, 8) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      {==}
                    case 1n+step_0_1_2_3_4:
                      match step_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(False{}, 5n+step_0_1_2_3_4, 8) == G.Cheat{} : G.Order}, L.false_is_not_true(during))
                        case 1n+step_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(False{}, 5n+step_0_1_2_3_4, 8) == G.Cheat{} : G.Order}, L.false_is_not_true(during))

def L.late_False_0(+step: Nat, +before: {Nat.is_lt(0n, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 0n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 0n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      {==}

def L.late_False_1(+step: Nat, +before: {Nat.is_lt(1n, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 1n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 1n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(False{}, 1n, G.Proto.expected(False{}, 1n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          {==}

def L.late_False_2(+step: Nat, +before: {Nat.is_lt(2n, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 2n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(False{}, 1n, G.Proto.expected(False{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(False{}, 2n, G.Proto.expected(False{}, 2n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              {==}

def L.late_False_3(+step: Nat, +before: {Nat.is_lt(3n, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 3n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(False{}, 1n, G.Proto.expected(False{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(False{}, 2n, G.Proto.expected(False{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(False{}, 3n, G.Proto.expected(False{}, 3n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                case 1n+step_0_1_2_3:
                  {==}

def L.late_False_4(+step: Nat, +before: {Nat.is_lt(4n, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(False{}, 1n, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(False{}, 2n, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(False{}, 3n, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      Empty.absurd({G.Proto.order(False{}, 4n, G.Proto.expected(False{}, 4n)) == G.Cheat{} : G.Order}, L.false_is_not_true(before))
                    case 1n+step_0_1_2_3_4:
                      {==}

def L.late_False(+step: Nat, +earlier: Nat, +before: {Nat.is_lt(earlier, step) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, earlier)) == G.Cheat{} : G.Order}:
  match earlier:
    case 0n:
      L.late_False_0(step, before)
    case 1n+earlier_0:
      match earlier_0:
        case 0n:
          L.late_False_1(step, before)
        case 1n+earlier_0_1:
          match earlier_0_1:
            case 0n:
              L.late_False_2(step, before)
            case 1n+earlier_0_1_2:
              match earlier_0_1_2:
                case 0n:
                  L.late_False_3(step, before)
                case 1n+earlier_0_1_2_3:
                  match earlier_0_1_2_3:
                    case 0n:
                      L.late_False_4(step, before)
                    case 1n+earlier_0_1_2_3_4:
                      {==}

def L.early_False_0(+step: Nat, +after: {Nat.is_lt(step, 0n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 0n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      Empty.absurd({G.Proto.order(False{}, 0n, G.Proto.expected(False{}, 0n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
    case 1n+r:
      Empty.absurd({G.Proto.order(False{}, 1n+r, G.Proto.expected(False{}, 0n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_False_1(+step: Nat, +after: {Nat.is_lt(step, 1n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 1n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          Empty.absurd({G.Proto.order(False{}, 1n, G.Proto.expected(False{}, 1n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
        case 1n+step_0_x:
          Empty.absurd({G.Proto.order(False{}, 2n+step_0_x, G.Proto.expected(False{}, 1n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_False_2(+step: Nat, +after: {Nat.is_lt(step, 2n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 2n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              Empty.absurd({G.Proto.order(False{}, 2n, G.Proto.expected(False{}, 2n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
            case 1n+step_0_1_x:
              Empty.absurd({G.Proto.order(False{}, 3n+step_0_1_x, G.Proto.expected(False{}, 2n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_False_3(+step: Nat, +after: {Nat.is_lt(step, 3n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 3n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  Empty.absurd({G.Proto.order(False{}, 3n, G.Proto.expected(False{}, 3n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
                case 1n+step_0_1_2_x:
                  Empty.absurd({G.Proto.order(False{}, 4n+step_0_1_2_x, G.Proto.expected(False{}, 3n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_False_4(+step: Nat, +after: {Nat.is_lt(step, 4n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, 4n)) == G.Hold{} : G.Order}:
  match step:
    case 0n:
      {==}
    case 1n+step_0:
      match step_0:
        case 0n:
          {==}
        case 1n+step_0_1:
          match step_0_1:
            case 0n:
              {==}
            case 1n+step_0_1_2:
              match step_0_1_2:
                case 0n:
                  {==}
                case 1n+step_0_1_2_3:
                  match step_0_1_2_3:
                    case 0n:
                      Empty.absurd({G.Proto.order(False{}, 4n, G.Proto.expected(False{}, 4n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))
                    case 1n+step_0_1_2_3_x:
                      Empty.absurd({G.Proto.order(False{}, 5n+step_0_1_2_3_x, G.Proto.expected(False{}, 4n)) == G.Hold{} : G.Order}, L.false_is_not_true(after))

def L.early_False(+step: Nat, +later: Nat, +after: {Nat.is_lt(step, later) == True{} : Bool}, +during: {Nat.is_lt(later, 5n) == True{} : Bool}) -> {G.Proto.order(False{}, step, G.Proto.expected(False{}, later)) == G.Hold{} : G.Order}:
  match later:
    case 0n:
      L.early_False_0(step, after)
    case 1n+later_0:
      match later_0:
        case 0n:
          L.early_False_1(step, after)
        case 1n+later_0_1:
          match later_0_1:
            case 0n:
              L.early_False_2(step, after)
            case 1n+later_0_1_2:
              match later_0_1_2:
                case 0n:
                  L.early_False_3(step, after)
                case 1n+later_0_1_2_3:
                  match later_0_1_2_3:
                    case 0n:
                      L.early_False_4(step, after)
                    case 1n+later_0_1_2_3_4:
                      match later_0_1_2_3_4:
                        case 0n:
                          Empty.absurd({G.Proto.order(False{}, step, G.Proto.expected(False{}, 5n+later_0_1_2_3_4)) == G.Hold{} : G.Order}, L.false_is_not_true(during))
                        case 1n+later_0_1_2_3_4_x:
                          Empty.absurd({G.Proto.order(False{}, step, G.Proto.expected(False{}, 5n+later_0_1_2_3_4)) == G.Hold{} : G.Order}, L.false_is_not_true(during))

def Laws.setup_messages_in_order(host, step, during):
  match host:
    case True{}:
      L.in_order_True(step, during)
    case False{}:
      L.in_order_False(step, during)

def Laws.late_setup_message_is_cheat(host, step, earlier, before):
  match host:
    case True{}:
      L.late_True(step, earlier, before)
    case False{}:
      L.late_False(step, earlier, before)

def Laws.early_setup_message_waits(host, step, later, after, during):
  match host:
    case True{}:
      L.early_True(step, later, after, during)
    case False{}:
      L.early_False(step, later, after, during)

def Laws.no_move_before_the_deal(host, step, during):
  match host:
    case True{}:
      L.no_move_True(step, during)
    case False{}:
      L.no_move_False(step, during)

def Laws.moves_after_the_deal(host, step, done):
  %Equal.sym(Bool, Nat.is_ge(step, 5n), True{}, done) : {G.Proto.order.move(_) == G.Take{} : G.Order}
  {==}

def Laws.blue_never_receives_its_own_shuffle(step):
  {==}

def Laws.red_never_receives_its_own_shuffle(step):
  {==}

def Laws.coin_must_match_its_commitment(matches, bit, accepted):
  accepted

def Laws.honest_coin_accepted():
  {==}
