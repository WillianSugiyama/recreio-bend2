import Base

# Rules of the game. LAWS.bend states what must always hold; this file implements it.
# Board: 7x7. A square is a Cell: a column and a row, each 0..6, so every Cell is on the board.
# Row 0 is the top (red's back row), row 6 the bottom (blue's back row). The web page numbers the
# squares 0..48 (row * 7 + col) and uses 49 for "no square"; only the api_* functions convert.

# ================================================================ small helpers

# The board's width (and height), and the number used for "no square".
def W() -> U32:
  7

def NONE() -> U32:
  49

def sel(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Bool.same(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

# xorshift32: the pseudo-random step used by simulations (never for the card draw itself).
def rng(+x: U32) -> U32:
  +a = U32.xor(x, U32.shln(x, 13n))
  +b = U32.xor(a, U32.shrn(a, 17n))
  U32.xor(b, U32.shln(b, 5n))

def mix(+x: U32) -> U32:
  rng((x * 2654435761 + 1 : U32))

def U32s.has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(h, x) || U32s.has(t, x)

def U32s.len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+U32s.len(t)

def U32s.nth(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      99
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      U32s.nth(t, p)

def U32s.count.add(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

def U32s.count(xs: List<&2, U32>, +x: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      U32s.count.add(U32.is_eq(h, x), U32s.count(t, x))

def U32s.remove.go(hit: Bool, h: U32, t: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match hit:
    case True{}:
      t
    case False{}:
      h <> rest

# The list without its first `x`.
def U32s.remove(xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      U32s.remove.go(U32.is_eq(h, x), h, t, U32s.remove(t, x))

def U32s.replace.go(hit: Bool, h: U32, t: List<&2, U32>, y: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match hit:
    case True{}:
      y <> t
    case False{}:
      h <> rest

# The list with its first `x` replaced by `y`.
def U32s.replace(xs: List<&2, U32>, +x: U32, +y: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      U32s.replace.go(U32.is_eq(h, x), h, t, y, U32s.replace(t, x, y))

def U32s.append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> U32s.append(t, ys)

def U32s.range(+n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      U32s.append(U32s.range(p), [U32.from_nat(p)])

def U32s.sum_mix(xs: List<&2, U32>, +salt: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (mix((h + salt : U32)) + U32s.sum_mix(t, salt) : U32)

# ================================================================ squares

type Fin7 is Data:
  F0{}
  F1{}
  F2{}
  F3{}
  F4{}
  F5{}
  F6{}

def Fin7.nat(f: Fin7) -> Nat:
  match f:
    case F0{}:
      0n
    case F1{}:
      1n
    case F2{}:
      2n
    case F3{}:
      3n
    case F4{}:
      4n
    case F5{}:
      5n
    case F6{}:
      6n

def Fin7.of_nat(n: Nat) -> Maybe<&2, Fin7>:
  match n:
    case 0n:
      Some{F0{}}
    case 1n:
      Some{F1{}}
    case 2n:
      Some{F2{}}
    case 3n:
      Some{F3{}}
    case 4n:
      Some{F4{}}
    case 5n:
      Some{F5{}}
    case 6n:
      Some{F6{}}
    case _:
      None{}

def Fin7.down(ok: Bool, n: Nat, d: Nat) -> Maybe<&2, Fin7>:
  match ok:
    case True{}:
      Fin7.of_nat(Nat.sub(n, d))
    case False{}:
      None{}

# `f` moved by `d` (up when `plus`), or None when it leaves the board.
def Fin7.shift(+f: Fin7, +d: Nat, plus: Bool) -> Maybe<&2, Fin7>:
  match plus:
    case True{}:
      Fin7.of_nat(Nat.add(Fin7.nat(f), d))
    case False{}:
      Fin7.down(Nat.is_le(d, Fin7.nat(f)), Fin7.nat(f), d)

type Cell is Data:
  Cell{col: Fin7, row: Fin7}

def Cell.eq(a: Cell, b: Cell) -> Bool:
  match a b:
    case Cell{ac, ar} Cell{bc, br}:
      Nat.is_eq(Fin7.nat(ac), Fin7.nat(bc)) && Nat.is_eq(Fin7.nat(ar), Fin7.nat(br))

def Cell.sel(c: Bool, a: Cell, b: Cell) -> Cell:
  match c:
    case True{}:
      a
    case False{}:
      b

# Whether `m` holds the cell `c`.
def Cell.is(m: Maybe<&2, Cell>, +c: Cell) -> Bool:
  match m:
    case Some{x}:
      Cell.eq(x, c)
    case None{}:
      False{}

def Cell.none(m: Maybe<&2, Cell>) -> Bool:
  match m:
    case Some{_}:
      False{}
    case None{}:
      True{}

def Cell.both(c: Maybe<&2, Fin7>, r: Maybe<&2, Fin7>) -> Maybe<&2, Cell>:
  match c r:
    case Some{x} Some{y}:
      Some{Cell{x, y}}
    case _ _:
      None{}

# The page's number for a cell: row * 7 + col.
def Cell.u32(c: Cell) -> U32:
  match c:
    case Cell{col, row}:
      (U32.from_nat(Fin7.nat(row)) * 7 + U32.from_nat(Fin7.nat(col)) : U32)

def Cell.of_u32(+x: U32) -> Maybe<&2, Cell>:
  Cell.both(Fin7.of_nat(U32.to_nat((x % 7 : U32))), Fin7.of_nat(U32.to_nat((x / 7 : U32))))

def Cell.or_corner(m: Maybe<&2, Cell>) -> Cell:
  match m:
    case Some{c}:
      c
    case None{}:
      Cell{F0{}, F0{}}

def Cell.code(m: Maybe<&2, Cell>) -> U32:
  match m:
    case Some{c}:
      Cell.u32(c)
    case None{}:
      NONE()

def Fin7s.all() -> List<&2, Fin7>:
  [F0{}, F1{}, F2{}, F3{}, F4{}, F5{}, F6{}]

def Cells.row(cs: List<&2, Fin7>, +r: Fin7, rest: List<&2, Cell>) -> List<&2, Cell>:
  match cs:
    case Nil{}:
      rest
    case Con{c, t}:
      Cell{c, r} <> Cells.row(t, r, rest)

def Cells.rows(rs: List<&2, Fin7>) -> List<&2, Cell>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Cells.row(Fin7s.all(), r, Cells.rows(t))

# All 49 cells.
def Cells.all() -> List<&2, Cell>:
  Cells.rows(Fin7s.all())

def Cells.has(xs: List<&2, Cell>, +x: Cell) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Cell.eq(h, x) || Cells.has(t, x)

def Cells.len(xs: List<&2, Cell>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Cells.len(t)

def Cells.take(n: Nat, xs: List<&2, Cell>) -> List<&2, Cell>:
  match n xs:
    case 0n _:
      Nil{}
    case _ Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      h <> Cells.take(p, t)

def Cells.append(xs: List<&2, Cell>, ys: List<&2, Cell>) -> List<&2, Cell>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> Cells.append(t, ys)

# ================================================================ sides

# ts: union
type Side is Data:
  Blue{}
  Red{}

def Side.other(s: Side) -> Side:
  match s:
    case Blue{}:
      Red{}
    case Red{}:
      Blue{}

def Side.is_blue(s: Side) -> Bool:
  match s:
    case Blue{}:
      True{}
    case Red{}:
      False{}

def Side.of_bool(blue: Bool) -> Side:
  match blue:
    case True{}:
      Blue{}
    case False{}:
      Red{}

# 0 is blue, anything else red.
def Side.of_code(c: U32) -> Side:
  Side.of_bool(U32.is_zero(c))

def Side.same(a: Side, b: Side) -> Bool:
  Bool.same(Side.is_blue(a), Side.is_blue(b))

def Side.code(s: Side) -> U32:
  sel(Side.is_blue(s), 0, 1)

# The square where each side's teacher starts (the goal): column 3 of its back row.
def Side.home(s: Side) -> Cell:
  match s:
    case Blue{}:
      Cell{F3{}, F6{}}
    case Red{}:
      Cell{F3{}, F0{}}

# ================================================================ cards

# One step of a card: how many squares sideways and forward, and to which side.
type Step is Data:
  Step{right: Bool, dx: Nat, up: Bool, dy: Nat}

# The same step mirrored left <-> right.
def Step.mirror(s: Step) -> Step:
  match s:
    case Step{r, dx, u, dy}:
      Step{Bool.not(r), dx, u, dy}

# The same step flipped up <-> down.
def Step.flip(s: Step) -> Step:
  match s:
    case Step{r, dx, u, dy}:
      Step{r, dx, Bool.not(u), dy}

# A step that only goes up or down.
def Step.is_vertical(s: Step) -> Bool:
  match s:
    case Step{_, dx, _, _}:
      Nat.is_eq(dx, 0n)

# Two steps that land on the same square (a 0-square part has no direction).
def Step.same(a: Step, b: Step) -> Bool:
  match a b:
    case Step{ar, +adx, au, +ady} Step{br, bdx, bu, bdy}:
      Nat.is_eq(adx, bdx) && Nat.is_eq(ady, bdy) && (Nat.is_eq(adx, 0n) || Bool.same(ar, br)) && (Nat.is_eq(ady, 0n) || Bool.same(au, bu))

def Step.reach(s: Step) -> Nat:
  match s:
    case Step{_, dx, _, dy}:
      Nat.max(dx, dy)








# Where a step leads from cell `sq` for `side`, or None off the board.
# Steps are written for blue (up = toward row 0); red sees the board turned around.
# Steps are written for blue (up = toward row 0); red sees the board turned around.
def Step.target(st: Step, sq: Cell, side: Side) -> Maybe<&2, Cell>:
  match st sq:
    case Step{r, dx, u, dy} Cell{c, w}:
      +red = Bool.not(Side.is_blue(side))
      Cell.both(Fin7.shift(c, dx, Bool.xor(r, red)), Fin7.shift(w, dy, Bool.not(Bool.xor(u, red))))

type Card is Data:
  Card{id: U32, name: String, steps: List<&2, Step>}

# How far a step goes sideways: 1, 2 or 3 squares (never 0, so a sideways step is never vertical).
type Dist is Data:
  Sq1{}
  Sq2{}
  Sq3{}

def Dist.nat(d: Dist) -> Nat:
  match d:
    case Sq1{}:
      1n
    case Sq2{}:
      2n
    case Sq3{}:
      3n

# A card is written as shapes, and each shape always gives its steps in pairs, so the deck
# laws hold by construction:
#   Sideways{dx, up, dy}: dx squares to the left AND to the right (dy forward or back)
#   Straight{dy}: dy squares straight up AND straight down
type Shape is Data:
  Sideways{dx: Dist, up: Bool, dy: Nat}
  Straight{dy: Dist}

def Shape.steps(sh: Shape, rest: List<&2, Step>) -> List<&2, Step>:
  match sh:
    case Sideways{+d, +u, +dy}:
      Step{False{}, Dist.nat(d), u, dy} <> Step{True{}, Dist.nat(d), u, dy} <> rest
    case Straight{+d}:
      Step{True{}, 0n, False{}, Dist.nat(d)} <> Step{True{}, 0n, True{}, Dist.nat(d)} <> rest

def Shapes.steps(xs: List<&2, Shape>) -> List<&2, Step>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Shape.steps(h, Shapes.steps(t))

type CardDef is Data:
  CardDef{id: U32, name: String, shapes: List<&2, Shape>}

def Card.make(d: CardDef) -> Card:
  match d:
    case CardDef{i, n, sh}:
      Card{i, n, Shapes.steps(sh)}

# The 18 cards, named after football plays.
def deck_defs() -> List<&2, CardDef>:
  [
    CardDef{0, "Toque", [Sideways{Sq1{}, True{}, 0n}, Straight{Sq1{}}]},
    CardDef{1, "Tabela", [Sideways{Sq1{}, False{}, 1n}, Sideways{Sq1{}, True{}, 1n}]},
    CardDef{2, "Abertura", [Sideways{Sq2{}, True{}, 0n}, Straight{Sq1{}}]},
    CardDef{3, "Triangulação", [Sideways{Sq1{}, True{}, 1n}, Straight{Sq1{}}]},
    CardDef{4, "Lançamento", [Sideways{Sq1{}, True{}, 0n}, Straight{Sq2{}}]},
    CardDef{5, "Chutão", [Sideways{Sq1{}, True{}, 0n}, Straight{Sq3{}}]},
    CardDef{6, "Drible", [Sideways{Sq1{}, False{}, 2n}, Sideways{Sq1{}, True{}, 2n}]},
    CardDef{7, "Chapéu", [Sideways{Sq2{}, False{}, 1n}, Sideways{Sq2{}, True{}, 1n}]},
    CardDef{8, "Pelada", [Sideways{Sq1{}, True{}, 0n}, Sideways{Sq1{}, True{}, 1n}, Straight{Sq1{}}]},
    CardDef{9, "Cruzamento", [Sideways{Sq2{}, True{}, 1n}, Straight{Sq1{}}]},
    CardDef{10, "Enfiada", [Sideways{Sq1{}, True{}, 1n}, Straight{Sq2{}}]},
    CardDef{11, "Bicicleta", [Sideways{Sq2{}, False{}, 2n}, Sideways{Sq2{}, True{}, 2n}, Sideways{Sq1{}, True{}, 0n}]},
    CardDef{12, "Inversão", [Sideways{Sq3{}, True{}, 0n}, Straight{Sq1{}}]},
    CardDef{13, "Recuo", [Sideways{Sq1{}, False{}, 1n}, Straight{Sq1{}}]},
    CardDef{14, "Marcação", [Sideways{Sq1{}, False{}, 1n}, Sideways{Sq1{}, True{}, 0n}, Straight{Sq2{}}]},
    CardDef{15, "Retranca", [Sideways{Sq1{}, False{}, 2n}, Straight{Sq1{}}]},
    CardDef{16, "Arrancada", [Sideways{Sq1{}, True{}, 2n}, Straight{Sq1{}}]},
    CardDef{17, "Contra-ataque", [Sideways{Sq3{}, True{}, 3n}, Sideways{Sq1{}, False{}, 1n}, Sideways{Sq1{}, True{}, 1n}]}
  ]

def CardDefs.make(ds: List<&2, CardDef>) -> List<&2, Card>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Card.make(d) <> CardDefs.make(t)

def CardDefs.nth(ds: List<&2, CardDef>, n: Nat) -> CardDef:
  match ds n:
    case Nil{} _:
      CardDef{99, "", Nil{}}
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      CardDefs.nth(t, p)

def deck() -> List<&2, Card>:
  CardDefs.make(deck_defs())

def Steps.has(xs: List<&2, Step>, +s: Step) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Step.same(h, s) || Steps.has(t, s)



def Steps.max_reach(xs: List<&2, Step>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(Step.reach(h), Steps.max_reach(t))

# The ids of the cards, in deck order (0..17).
def Cards.ids(cs: List<&2, Card>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Card{i, _, _}, t}:
      i <> Cards.ids(t)

def Cards.len(cs: List<&2, Card>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Cards.len(t)

def Cards.max_reach(cs: List<&2, Card>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{Card{_, _, st}, t}:
      Nat.max(Steps.max_reach(st), Cards.max_reach(t))

def Cards.steps_of.pick(hit: Bool, a: List<&2, Step>, b: List<&2, Step>) -> List<&2, Step>:
  match hit:
    case True{}:
      a
    case False{}:
      b

def Cards.steps_of(cs: List<&2, Card>, +id: U32) -> List<&2, Step>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Card{cid, _, st}, t}:
      Cards.steps_of.pick(U32.is_eq(cid, id), st, Cards.steps_of(t, id))

def Steps.len(xs: List<&2, Step>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Steps.len(t)

def Steps.nth(xs: List<&2, Step>, n: Nat) -> Step:
  match xs n:
    case Nil{} _:
      Step{True{}, 0n, True{}, 0n}
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      Steps.nth(t, p)

def Step.pack(s: Step) -> U32:
  match s:
    case Step{r, dx, u, dy}:
      +x = U32.from_nat(dx)
      +y = U32.from_nat(dy)
      (sel(r, (3 + x : U32), (3 - x : U32)) * 8 + sel(u, (3 + y : U32), (3 - y : U32)) : U32)

def deck_size() -> Nat:
  Cards.len(deck())

def deck_card(i: Nat) -> Card:
  Card.make(CardDefs.nth(deck_defs(), i))

def deck_max_step() -> Nat:
  Cards.max_reach(deck())

def card_has(c: Card, s: Step) -> Bool:
  match c:
    case Card{_, _, st}:
      Steps.has(st, s)

def card_steps(id: U32) -> List<&2, Step>:
  Cards.steps_of(deck(), id)

# ================================================================ card draw

# A player's secret for the draw, chosen at random on their own device.
# Each player's secret, chosen at random on their own device: a coin for who starts and a list
# of numbers, one per card drawn.
type Secret is Data:
  Secret{coin: Bool, picks: List<&2, Nat>}

# Who got what: the 2 blue cards, the 2 red cards and the table card.
type Deal is Data:
  Deal{blue: List<&2, U32>, red: List<&2, U32>, table: U32}

def Deal.hand_of(d: Deal, s: Side) -> List<&2, U32>:
  match d s:
    case Deal{b, _, _} Blue{}:
      b
    case Deal{_, r, _} Red{}:
      r

def U32s.nth_or(xs: List<&2, U32>, n: Nat, d: U32) -> U32:
  match xs n:
    case Nil{} _:
      d
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      U32s.nth_or(t, p, d)

# The card at position `r mod length` of `xs` (card 0 if `xs` were ever empty).
def draw_pick(+xs: List<&2, U32>, r: U32) -> U32:
  U32s.nth_or(xs, U32.to_nat((r % U32.from_nat(U32s.len(xs)) : U32)), 0)

# Draws `n` different cards from `xs` with seed `r`.
def draw_n(n: Nat, +xs: List<&2, U32>, +r: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +c = draw_pick(xs, r)
      c <> draw_n(p, U32s.remove(xs, c), rng(r))

def Deal.of_list(cs: List<&2, U32>) -> Deal:
  match cs:
    case Con{a, Con{b, Con{c, Con{d, Con{e, _}}}}}:
      Deal{[a, b], [c, d], e}
    case _:
      Deal{[0, 1], [2, 3], 4}

# The draw: the remaining deck is turned by the sum of both players' numbers and its top card is
# drawn, five times. Whatever one player picks, the other's number can still bring any remaining
# card to the top, so neither decides the deal alone (LAWS.bend proves it).
def Nats.head0(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, _}:
      h

def Nats.tail(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def U32s.rot1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      U32s.append(t, [h])

# The list turned `k` times (the top card goes to the bottom each time).
def U32s.rotate(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      xs
    case 1n+p:
      U32s.rotate(p, U32s.rot1(xs))

def Draw.k(+bs: List<&2, Nat>, +rs: List<&2, Nat>) -> Nat:
  Nat.add(Nats.head0(bs), Nats.head0(rs))

# Draws `n` cards from the already turned deck `rot`.
def Draw.go(n: Nat, rot: List<&2, U32>, +bs: List<&2, Nat>, +rs: List<&2, Nat>) -> List<&2, U32>:
  match n rot:
    case 0n _:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{c, rest}:
      c <> Draw.go(p, U32s.rotate(Draw.k(Nats.tail(bs), Nats.tail(rs)), rest), Nats.tail(bs), Nats.tail(rs))

def deal_from(blue: Secret, red: Secret) -> Deal:
  match blue red:
    case Secret{_, +bs} Secret{_, +rs}:
      Deal.of_list(Draw.go(5n, U32s.rotate(Draw.k(bs, rs), Cards.ids(deck())), bs, rs))

# A secret from one random number (for games against the bot).
def Secret.of_key(+k: U32) -> Secret:
  +k1 = rng(k)
  +k2 = rng(k1)
  +k3 = rng(k2)
  +k4 = rng(k3)
  +k5 = rng(k4)
  Secret{U32.is_even(k5), [U32.to_nat((k % 18 : U32)), U32.to_nat((k1 % 18 : U32)), U32.to_nat((k2 % 18 : U32)), U32.to_nat((k3 % 18 : U32)), U32.to_nat((k4 % 18 : U32))]}

def U32s.distinct(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(U32s.has(t, h)), U32s.distinct(t))

def U32s.all_in(xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32s.has(ys, h), U32s.all_in(t, ys))

def Deal.five_ok(+xs: List<&2, U32>) -> Bool:
  Bool.and(U32s.distinct(xs), U32s.all_in(xs, Cards.ids(deck())))

# Two cards for each player and one on the table: 5 different cards, all from the deck.
def Deal.is_valid(d: Deal) -> Bool:
  match d:
    case Deal{Con{a, Con{b, Nil{}}}, Con{c, Con{e, Nil{}}}, t}:
      Deal.five_ok([a, b, c, e, t])
    case _:
      False{}

# ================================================================ setup

# The starting state: both players' secrets.
type Setup is Data:
  Setup{blue_secret: Secret, red_secret: Secret}

def Setup.deal(s: Setup) -> Deal:
  match s:
    case Setup{b, r}:
      deal_from(b, r)

# Who starts: equal coins, blue; different coins, red. Neither coin alone decides it.
def Coin.side(blue: Bool, red: Bool) -> Side:
  Side.of_bool(Bool.same(blue, red))

def Setup.starter(s: Setup) -> Side:
  match s:
    case Setup{Secret{bc, _}, Secret{rc, _}}:
      Coin.side(bc, rc)

# ================================================================ board

type Piece is Data:
  Piece{side: Side, teacher: Bool, square: Cell}

# 0 empty, 1 blue student, 2 blue teacher, 3 red student, 4 red teacher.
def Piece.code(side: Side, teacher: Bool) -> U32:
  (sel(Side.is_blue(side), 1, 3) + sel(teacher, 1, 0) : U32)

def Pieces.code_at(ps: List<&2, Piece>, +sq: Cell) -> U32:
  match ps:
    case Nil{}:
      0
    case Con{Piece{s, t, q}, rest}:
      sel(Cell.eq(q, sq), Piece.code(s, t), Pieces.code_at(rest, sq))

def Code.is_side(+c: U32, side: Side) -> Bool:
  match side:
    case Blue{}:
      U32.is_eq(c, 1) || U32.is_eq(c, 2)
    case Red{}:
      U32.is_eq(c, 3) || U32.is_eq(c, 4)

def Pieces.side_at(ps: List<&2, Piece>, sq: Cell, side: Side) -> Bool:
  Code.is_side(Pieces.code_at(ps, sq), side)

def Pieces.teacher_of.pick(hit: Bool, q: Cell, rest: Maybe<&2, Cell>) -> Maybe<&2, Cell>:
  match hit:
    case True{}:
      Some{q}
    case False{}:
      rest

# Where `side`'s teacher stands (None once captured).
def Pieces.teacher_of(ps: List<&2, Piece>, +side: Side) -> Maybe<&2, Cell>:
  match ps:
    case Nil{}:
      None{}
    case Con{Piece{s, t, q}, rest}:
      Pieces.teacher_of.pick(Side.same(s, side) && t, q, Pieces.teacher_of(rest, side))

def Pieces.len(ps: List<&2, Piece>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Pieces.len(t)

def Pieces.capture.go(hit: Bool, p: Piece, rest: List<&2, Piece>) -> List<&2, Piece>:
  match hit:
    case True{}:
      rest
    case False{}:
      p <> rest

# The pieces of `enemy` standing on `sq` leave the board.
def Pieces.capture(ps: List<&2, Piece>, +sq: Cell, +enemy: Side) -> List<&2, Piece>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Piece{+s, +t, +q}, rest}:
      Pieces.capture.go(Side.same(s, enemy) && Cell.eq(q, sq), Piece{s, t, q}, Pieces.capture(rest, sq, enemy))

def Pieces.move(ps: List<&2, Piece>, +from: Cell, +to: Cell) -> List<&2, Piece>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Piece{s, t, +q}, rest}:
      Piece{s, t, Cell.sel(Cell.eq(q, from), to, q)} <> Pieces.move(rest, from, to)

def Pieces.key(ps: List<&2, Piece>) -> U32:
  match ps:
    case Nil{}:
      0
    case Con{Piece{s, t, q}, rest}:
      (mix((Piece.code(s, t) * 64 + Cell.u32(q) : U32)) + Pieces.key(rest) : U32)

def Pieces.start() -> List<&2, Piece>:
  [Piece{Blue{}, False{}, Cell{F0{}, F6{}}}, Piece{Blue{}, False{}, Cell{F1{}, F6{}}}, Piece{Blue{}, False{}, Cell{F2{}, F6{}}}, Piece{Blue{}, True{}, Cell{F3{}, F6{}}}, Piece{Blue{}, False{}, Cell{F4{}, F6{}}}, Piece{Blue{}, False{}, Cell{F5{}, F6{}}}, Piece{Blue{}, False{}, Cell{F6{}, F6{}}},
   Piece{Red{}, False{}, Cell{F0{}, F0{}}}, Piece{Red{}, False{}, Cell{F1{}, F0{}}}, Piece{Red{}, False{}, Cell{F2{}, F0{}}}, Piece{Red{}, True{}, Cell{F3{}, F0{}}}, Piece{Red{}, False{}, Cell{F4{}, F0{}}}, Piece{Red{}, False{}, Cell{F5{}, F0{}}}, Piece{Red{}, False{}, Cell{F6{}, F0{}}}]

# ================================================================ game

# ts: union
type Outcome is Data:
  Ongoing{}
  Winner{side: Side}
  Draw{}

def Outcome.is_win(o: Outcome) -> Bool:
  match o:
    case Winner{_}:
      True{}
    case _:
      False{}

def Outcome.is_over(o: Outcome) -> Bool:
  match o:
    case Ongoing{}:
      False{}
    case _:
      True{}

# 0 ongoing, 1 blue won, 2 red won, 3 draw.
def Outcome.code(o: Outcome) -> U32:
  match o:
    case Ongoing{}:
      0
    case Winner{s}:
      sel(Side.is_blue(s), 1, 2)
    case Draw{}:
      3

# `history` holds the keys of the positions since the last capture (a capture makes old ones unreachable).
type Game is Data:
  Game{turn: Side, pieces: List<&2, Piece>, blue: List<&2, U32>, red: List<&2, U32>, table: U32, quiet: Nat, history: List<&2, U32>, result: Outcome}

type Action is Data:
  Action{card: U32, from: Cell, to: Cell}

def Action.card(m: Action) -> U32:
  match m:
    case Action{c, _, _}:
      c

def Action.from(m: Action) -> Cell:
  match m:
    case Action{_, f, _}:
      f

def to_of(m: Action) -> Cell:
  match m:
    case Action{_, _, t}:
      t

def Action.same(a: Action, b: Action) -> Bool:
  match a b:
    case Action{c1, f1, t1} Action{c2, f2, t2}:
      U32.is_eq(c1, c2) && Cell.eq(f1, f2) && Cell.eq(t1, t2)

def Action.code(m: Action) -> U32:
  match m:
    case Action{c, f, t}:
      (c * 2401 + Cell.u32(f) * 49 + Cell.u32(t) : U32)

def Action.of_code(+n: U32) -> Action:
  Action{(n / 2401 : U32), Cell.or_corner(Cell.of_u32(((n / 49 : U32) % 49 : U32))), Cell.or_corner(Cell.of_u32((n % 49 : U32)))}

# A code from the page names a move only if it reads back to itself (squares 0..48).
def Action.valid_code(+n: U32) -> Bool:
  U32.is_eq(Action.code(Action.of_code(n)), n)

def Actions.has(xs: List<&2, Action>, +m: Action) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Action.same(h, m) || Actions.has(t, m)

def Actions.nonempty(xs: List<&2, Action>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{_, _}:
      True{}

def Actions.len(xs: List<&2, Action>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Actions.len(t)

def Actions.nth(xs: List<&2, Action>, n: Nat) -> Action:
  match xs n:
    case Nil{} _:
      Action{99, Cell{F0{}, F0{}}, Cell{F0{}, F0{}}}
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      Actions.nth(t, p)

def Game.turn(g: Game) -> Side:
  match g:
    case Game{t, _, _, _, _, _, _, _}:
      t

def Game.pieces(g: Game) -> List<&2, Piece>:
  match g:
    case Game{_, p, _, _, _, _, _, _}:
      p

def Game.result(g: Game) -> Outcome:
  match g:
    case Game{_, _, _, _, _, _, _, r}:
      r

def Game.hand(g: Game, s: Side) -> List<&2, U32>:
  match g s:
    case Game{_, _, b, _, _, _, _, _} Blue{}:
      b
    case Game{_, _, _, r, _, _, _, _} Red{}:
      r

def Game.table(g: Game) -> U32:
  match g:
    case Game{_, _, _, _, t, _, _, _}:
      t

def Game.quiet(g: Game) -> Nat:
  match g:
    case Game{_, _, _, _, _, q, _, _}:
      q

def Game.history(g: Game) -> List<&2, U32>:
  match g:
    case Game{_, _, _, _, _, _, h, _}:
      h

# The key of a position: board, both hands, table card and turn (order-free, so the same
# position reached in a different order has the same key).
def Game.key(ps: List<&2, Piece>, b: List<&2, U32>, r: List<&2, U32>, +t: U32, turn: Side) -> U32:
  (Pieces.key(ps) + U32s.sum_mix(b, 100) + U32s.sum_mix(r, 200) + mix((t + 300 : U32)) + sel(Side.is_blue(turn), 0, 977) : U32)

def start_dealt(+starter: Side, d: Deal) -> Game:
  match d:
    case Deal{+b, +r, +t}:
      Game{starter, Pieces.start(), b, r, t, 0n, [Game.key(Pieces.start(), b, r, t, starter)], Ongoing{}}

def start(+setup: Setup) -> Game:
  start_dealt(Setup.starter(setup), Setup.deal(setup))

# ---- moves

def gen.add(skip: Bool, m: Action, acc: List<&2, Action>) -> List<&2, Action>:
  match skip:
    case True{}:
      acc
    case False{}:
      m <> acc

# A step that stays on the board adds the move unless it lands on one of the mover's own pieces.
def gen.add_to(t: Maybe<&2, Cell>, +card: U32, +from: Cell, +side: Side, +ps: List<&2, Piece>, acc: List<&2, Action>) -> List<&2, Action>:
  match t:
    case None{}:
      acc
    case Some{+to}:
      gen.add(Pieces.side_at(ps, to, side), Action{card, from, to}, acc)

# Every move of one piece with one card's steps.
def gen.steps(sts: List<&2, Step>, +card: U32, +from: Cell, +side: Side, +ps: List<&2, Piece>, acc: List<&2, Action>) -> List<&2, Action>:
  match sts:
    case Nil{}:
      acc
    case Con{st, rest}:
      gen.steps(rest, card, from, side, ps, gen.add_to(Step.target(st, from, side), card, from, side, ps, acc))

def gen.pieces.one(mine: Bool, sts: List<&2, Step>, card: U32, q: Cell, side: Side, ps: List<&2, Piece>, acc: List<&2, Action>) -> List<&2, Action>:
  match mine:
    case True{}:
      gen.steps(sts, card, q, side, ps, acc)
    case False{}:
      acc

def gen.pieces(it: List<&2, Piece>, +card: U32, +sts: List<&2, Step>, +side: Side, +ps: List<&2, Piece>, acc: List<&2, Action>) -> List<&2, Action>:
  match it:
    case Nil{}:
      acc
    case Con{Piece{s, _, +q}, rest}:
      gen.pieces(rest, card, sts, side, ps, gen.pieces.one(Side.same(s, side), sts, card, q, side, ps, acc))

def gen.cards(hand: List<&2, U32>, +side: Side, +ps: List<&2, Piece>, acc: List<&2, Action>) -> List<&2, Action>:
  match hand:
    case Nil{}:
      acc
    case Con{+c, rest}:
      gen.cards(rest, side, ps, gen.pieces(ps, c, card_steps(c), side, ps, acc))

def gen.if_ongoing(over: Bool, +g: Game) -> List<&2, Action>:
  match over:
    case True{}:
      Nil{}
    case False{}:
      gen.cards(Game.hand(g, Game.turn(g)), Game.turn(g), Game.pieces(g), Nil{})

# All legal moves of the player whose turn it is (none once the game is over).
def legal_moves(+g: Game) -> List<&2, Action>:
  gen.if_ongoing(Outcome.is_over(Game.result(g)), g)

def is_legal(+g: Game, m: Action) -> Bool:
  Actions.has(legal_moves(g), m)

# In this model a card is "proven" when it is in the mover's hand; online, the browser
# checks the cryptographic opening before handing the move to `play`.
def card_proven(+g: Game, m: Action) -> Bool:
  match m:
    case Action{c, _, _}:
      U32s.has(Game.hand(g, Game.turn(g)), c)

def outcome_after(win: Bool, mover: Side, draw: Bool) -> Outcome:
  match win draw:
    case True{} _:
      Winner{mover}
    case False{} True{}:
      Draw{}
    case False{} False{}:
      Ongoing{}

def hand_after(mine: Bool, h: List<&2, U32>, +card: U32, +table: U32) -> List<&2, U32>:
  match mine:
    case True{}:
      U32s.replace(h, card, table)
    case False{}:
      h

def history_after(captured: Bool, +key: U32, h: List<&2, U32>) -> List<&2, U32>:
  match captured:
    case True{}:
      [key]
    case False{}:
      key <> h

def quiet_after(captured: Bool, q: Nat) -> Nat:
  match captured:
    case True{}:
      0n
    case False{}:
      1n+q

# A draw: the current position (first in the history) has appeared 3 times, or 20 turns passed
# without a capture.
def Game.drawn(+h: List<&2, U32>, q: Nat) -> Bool:
  Nat.is_ge(U32s.count(h, U32s.nth(h, 0n)), 3n) || Nat.is_ge(q, 20n)

# Moving to `to` wins: it takes the enemy goalkeeper or reaches the enemy goal.
def won(+ps: List<&2, Piece>, +enemy: Side, +to: Cell) -> Bool:
  Cell.is(Pieces.teacher_of(ps, enemy), to) || Cell.eq(to, Side.home(enemy))

# The game after the move, once we know whether it won (kept apart so proofs can name `win`).
def apply.go(win: Bool, +turn: Side, +ps: List<&2, Piece>, +b: List<&2, U32>, +r: List<&2, U32>, +table: U32, q: Nat, h: List<&2, U32>, +card: U32, +from: Cell, +to: Cell) -> Game:
  +enemy = Side.other(turn)
  +captured = Pieces.side_at(ps, to, enemy)
  +ps2 = Pieces.move(Pieces.capture(ps, to, enemy), from, to)
  +b2 = hand_after(Side.is_blue(turn), b, card, table)
  +r2 = hand_after(Bool.not(Side.is_blue(turn)), r, card, table)
  +q2 = quiet_after(captured, q)
  +key = Game.key(ps2, b2, r2, card, enemy)
  +h2 = history_after(captured, key, h)
  +draw = Game.drawn(h2, q2)
  Game{enemy, ps2, b2, r2, card, q2, h2, outcome_after(win, turn, draw)}

# Plays a move already known to be legal.
def apply(g: Game, m: Action) -> Game:
  match g m:
    case Game{+turn, +ps, b, r, table, q, h, _} Action{card, from, +to}:
      apply.go(won(ps, Side.other(turn), to), turn, ps, b, r, table, q, h, card, from, to)

def play.go(legal: Bool, g: Game, m: Action) -> Game:
  match legal:
    case True{}:
      apply(g, m)
    case False{}:
      g

# Plays a move; an illegal move changes nothing.
def play(+g: Game, +m: Action) -> Game:
  play.go(is_legal(g, m), g, m)

def replay(moves: List<&2, Action>, g: Game) -> Game:
  match moves:
    case Nil{}:
      g
    case Con{m, rest}:
      replay(rest, play(g, m))

# The game after playing `moves` from the start (illegal moves are ignored).
def after(+setup: Setup, moves: List<&2, Action>) -> Game:
  replay(moves, start(setup))

def turn_of(g: Game) -> Side:
  Game.turn(g)

def outcome(g: Game) -> Outcome:
  Game.result(g)

def is_over(g: Game) -> Bool:
  Outcome.is_over(Game.result(g))

def has_winner(g: Game) -> Bool:
  Outcome.is_win(outcome(g))

# How many times the current position (board, cards and turn) has appeared in this game.
def repetitions(+setup: Setup, +moves: List<&2, Action>) -> Nat:
  +h = Game.history(after(setup, moves))
  U32s.count(h, U32s.nth(h, 0n))

# Turns played since the last capture (or since the start).
def quiet_turns(setup: Setup, moves: List<&2, Action>) -> Nat:
  Game.quiet(after(setup, moves))

def has_legal_move(+g: Game) -> Bool:
  Actions.nonempty(legal_moves(g))

def card_count(+g: Game) -> Nat:
  Nat.add(Nat.add(U32s.len(Game.hand(g, Blue{})), U32s.len(Game.hand(g, Red{}))), 1n)

def piece_count(g: Game) -> Nat:
  Pieces.len(Game.pieces(g))

# The square where the enemy teacher started.
def enemy_home(g: Game) -> Cell:
  Side.home(Side.other(Game.turn(g)))

# The square where the enemy teacher is now (NONE once captured).
def enemy_teacher_square(+g: Game) -> Maybe<&2, Cell>:
  Pieces.teacher_of(Game.pieces(g), Side.other(Game.turn(g)))

def enemy_at(+g: Game, square: Cell) -> Bool:
  Pieces.side_at(Game.pieces(g), square, Side.other(Game.turn(g)))

def own_at(+g: Game, square: Cell) -> Bool:
  Pieces.side_at(Game.pieces(g), square, Game.turn(g))

def own_cards(g: Game, s: Side) -> List<&2, U32>:
  Game.hand(g, s)

def table_card(g: Game) -> U32:
  Game.table(g)

# The same game with the enemy's hand (of player `s`) replaced by `cards`.
def with_enemy_hand(g: Game, s: Side, cards: List<&2, U32>) -> Game:
  match g s:
    case Game{t, p, b, _, tb, q, h, res} Blue{}:
      Game{t, p, b, cards, tb, q, h, res}
    case Game{t, p, _, r, tb, q, h, res} Red{}:
      Game{t, p, cards, r, tb, q, h, res}

def reveal_hand.go(known: Bool, h: List<&2, U32>, card: U32) -> List<&2, U32>:
  match known:
    case True{}:
      h
    case False{}:
      U32s.replace(h, 99, card)

# Online: the enemy just played `card`, proven by its cryptographic opening, from a hand we only
# partly know (99 = unknown). Put the card in place of an unknown slot, then play the move.
def reveal_hand(+h: List<&2, U32>, +card: U32) -> List<&2, U32>:
  reveal_hand.go(U32s.has(h, card), h, card)

def play_revealed(+g: Game, +m: Action) -> Game:
  match m:
    case Action{c, _, _}:
      play(with_enemy_hand(g, Side.other(Game.turn(g)), reveal_hand(Game.hand(g, Game.turn(g)), c)), m)

# ================================================================ what each player sees

# One player's screen: the board, their own two cards and the table card. Never the enemy's cards.
type View is Data:
  View{side: Side, own: List<&2, U32>, table: U32, turn: Side, pieces: List<&2, Piece>, quiet: Nat, history: List<&2, U32>, result: Outcome}

def View.make(s: Side, b: List<&2, U32>, r: List<&2, U32>, tb: U32, t: Side, p: List<&2, Piece>, q: Nat, h: List<&2, U32>, res: Outcome) -> View:
  match s:
    case Blue{}:
      View{Blue{}, b, tb, t, p, q, h, res}
    case Red{}:
      View{Red{}, r, tb, t, p, q, h, res}

def view(g: Game, s: Side) -> View:
  match g:
    case Game{t, p, b, r, tb, q, h, res}:
      View.make(s, b, r, tb, t, p, q, h, res)

def View.own(v: View) -> List<&2, U32>:
  match v:
    case View{_, o, _, _, _, _, _, _}:
      o

def View.table(v: View) -> U32:
  match v:
    case View{_, _, t, _, _, _, _, _}:
      t

def View.side(v: View) -> Side:
  match v:
    case View{s, _, _, _, _, _, _, _}:
      s

def View.result(v: View) -> Outcome:
  match v:
    case View{_, _, _, _, _, _, _, r}:
      r

def View.key(v: View) -> U32:
  match v:
    case View{_, _, _, _, _, _, h, _}:
      U32s.nth(h, 0n)

def View.guess.go(s: Side, o: List<&2, U32>, e: List<&2, U32>, tb: U32, t: Side, p: List<&2, Piece>, q: Nat, h: List<&2, U32>, res: Outcome) -> Game:
  match s:
    case Blue{}:
      Game{t, p, o, e, tb, q, h, res}
    case Red{}:
      Game{t, p, e, o, tb, q, h, res}

# A full game guessed from a view, with `enemy` as the enemy's hand.
def View.guess(v: View, enemy: List<&2, U32>) -> Game:
  match v:
    case View{s, o, tb, t, p, q, h, res}:
      View.guess.go(s, o, enemy, tb, t, p, q, h, res)

# A random enemy hand consistent with the view: 2 cards that are neither ours nor on the table.
def View.sample_enemy(+v: View, +r: U32) -> List<&2, U32>:
  draw_n(2n, U32s.remove(U32s.remove(U32s.remove(U32s.range(18n), View.table(v)), U32s.nth(View.own(v), 0n)), U32s.nth(View.own(v), 1n)), r)

def find_win.pick(hit: Bool, a: Action, b: Maybe<&2, Action>) -> Maybe<&2, Action>:
  match hit:
    case True{}:
      Some{a}
    case False{}:
      b

# ================================================================ simulations (chances and bot)

def find_win(ms: List<&2, Action>, +home: Cell, +tsq: Maybe<&2, Cell>) -> Maybe<&2, Action>:
  match ms:
    case Nil{}:
      None{}
    case Con{+m, rest}:
      find_win.pick(Cell.eq(to_of(m), home) || Cell.is(tsq, to_of(m)), m, find_win(rest, home, tsq))

def quick_move.pick(w: Maybe<&2, Action>, +ms: List<&2, Action>, r: U32) -> Action:
  match w:
    case None{}:
      Actions.nth(ms, U32.to_nat((r % U32.from_nat(Actions.len(ms)) : U32)))
    case Some{a}:
      a

# The move a quick simulated player makes: a winning move if there is one, else a random one.
def quick_move(+g: Game, +r: U32) -> Action:
  +ms = legal_moves(g)
  quick_move.pick(find_win(ms, enemy_home(g), enemy_teacher_square(g)), ms, r)

# Plays quick moves until the game ends (or `fuel` runs out, counted as a draw).
def playout(fuel: Nat, over: Bool, +g: Game, +r: U32) -> Outcome:
  match fuel over:
    case _ True{}:
      Game.result(g)
    case 0n False{}:
      Draw{}
    case 1n+f False{}:
      +g2 = play(g, quick_move(g, r))
      playout(f, is_over(g2), g2, rng(r))

# Out of `games` simulated games from here: how many blue won, red won, and were draws.
# ts: union
type Chances is Data:
  Chances{blue: Nat, red: Nat, draws: Nat, games: Nat}

def Chances.add(c: Chances, o: Outcome) -> Chances:
  match c o:
    case Chances{b, r, d, n} Winner{Blue{}}:
      Chances{1n+b, r, d, 1n+n}
    case Chances{b, r, d, n} Winner{Red{}}:
      Chances{b, 1n+r, d, 1n+n}
    case Chances{b, r, d, n} _:
      Chances{b, r, 1n+d, 1n+n}

def chances.run(n: Nat, +v: View, +r: U32, acc: Chances) -> Chances:
  match n:
    case 0n:
      acc
    case 1n+p:
      +g = View.guess(v, View.sample_enemy(v, r))
      chances.run(p, v, rng(rng(r)), Chances.add(acc, playout(240n, is_over(g), g, rng(r))))

def chances.all(o: Outcome, +n: Nat) -> Chances:
  match o:
    case Winner{Blue{}}:
      Chances{n, 0n, 0n, n}
    case Winner{Red{}}:
      Chances{0n, n, 0n, n}
    case _:
      Chances{0n, 0n, n, n}

def chances.go(over: Bool, +v: View, +n: Nat) -> Chances:
  match over:
    case True{}:
      chances.all(View.result(v), n)
    case False{}:
      chances.run(n, v, (mix(View.key(v)) + 1 : U32), Chances{0n, 0n, 0n, 0n})

def chances_n(+v: View, n: Nat) -> Chances:
  chances.go(Outcome.is_over(View.result(v)), v, n)

# Computed only from what one player can see, so the numbers cannot leak the enemy's cards.
def chances(+v: View) -> Chances:
  chances_n(v, 100n)

def Chances.wins_of(c: Chances, s: Side) -> Nat:
  match c s:
    case Chances{b, _, _, _} Blue{}:
      b
    case Chances{_, r, _, _} Red{}:
      r

def Chances.draws(c: Chances) -> Nat:
  match c:
    case Chances{_, _, d, _}:
      d

def Chances.total(c: Chances) -> Nat:
  match c:
    case Chances{b, r, d, _}:
      Nat.add(Nat.add(b, r), d)

def Chances.games(c: Chances) -> Nat:
  match c:
    case Chances{_, _, _, n}:
      n

def bot.points(o: Outcome, me: Side) -> U32:
  match o:
    case Winner{s}:
      sel(Side.same(s, me), 2, 0)
    case _:
      1

# ---- bot: decides from its own view only

# Score of one move for the bot: 2 per simulated win, 1 per draw, over `n` guesses of the enemy hand.
def bot.score(n: Nat, +v: View, +m: Action, +me: Side, +r: U32, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      +g = play(View.guess(v, View.sample_enemy(v, r)), m)
      +o = playout(240n, is_over(g), g, rng(r))
      bot.score(p, v, m, me, rng(rng(r)), (acc + bot.points(o, me) : U32))

def bot.keep(better: Bool, m: Action, best: Action) -> Action:
  match better:
    case True{}:
      m
    case False{}:
      best

def bot.best(ms: List<&2, Action>, +n: Nat, +v: View, +r: U32, best: Action, +best_score: U32) -> Action:
  match ms:
    case Nil{}:
      best
    case Con{+m, rest}:
      +s = bot.score(n, v, m, View.side(v), r, 0)
      +better = (best_score < s : U32)
      bot.best(rest, n, v, rng(r), bot.keep(better, m, best), sel(better, s, best_score))

def bot.by_level(lvl: Nat, +ms: List<&2, Action>, +v: View, +r: U32) -> Action:
  match lvl:
    case 0n:
      Actions.nth(ms, U32.to_nat((r % U32.from_nat(Actions.len(ms)) : U32)))
    case 1n:
      bot.best(ms, 24n, v, r, Actions.nth(ms, 0n), 0)
    case _:
      bot.best(ms, 160n, v, r, Actions.nth(ms, 0n), 0)

def bot.decide.go(w: Maybe<&2, Action>, ms: List<&2, Action>, v: View, lvl: Nat, r: U32) -> Action:
  match w:
    case None{}:
      bot.by_level(lvl, ms, v, r)
    case Some{a}:
      a

# The bot's move, decided only from what the bot can see. Level 0 easy, 1 medium, 2 hard.
def bot.decide(+v: View, lvl: Nat, +r: U32) -> Action:
  +g = View.guess(v, [99, 99])
  +ms = legal_moves(g)
  bot.decide.go(find_win(ms, enemy_home(g), enemy_teacher_square(g)), ms, v, lvl, r)

# ================================================================ invite code and messages

# The room the invited player joins. Both browsers connect to a relay (a Cloudflare Worker)
# with it; the relay only forwards messages and decides nothing: each browser checks every move.
# Every connection is outbound: no router ports to open.
type Invite is Data:
  Invite{room: U32}

# ---- numbers as text, bit by bit: reading back what was written is then provable (see PROOF.bend)

def Bit.char(b: Bool) -> Char:
  match b:
    case True{}:
      '1'
    case False{}:
      '0'

# The `n` bits of `w`, written in front of `rest`.
def Bits.show(n: Nat, w: Word(n), rest: String) -> String:
  match n:
    case 0n:
      rest
    case 1n+p:
      match w:
        case WCon{b, t}:
          SCon{Bit.char(b), Bits.show(p, t, rest)}

def Bits.bit.go(one: Bool, zero: Bool) -> Maybe<&2, Bool>:
  match one zero:
    case True{} _:
      Some{True{}}
    case False{} True{}:
      Some{False{}}
    case False{} False{}:
      None{}

def Bits.bit(+c: Char) -> Maybe<&2, Bool>:
  Bits.bit.go(Char.is_eq(c, '1'), Char.is_eq(c, '0'))

def Bits.cons(-p: Nat, b: Maybe<&2, Bool>, w: Maybe<&2, Word(p)>) -> Maybe<&2, Word(1n+p)>:
  match b w:
    case Some{x} Some{y}:
      Some{WCon{x, y}}
    case _ _:
      None{}

# The first `n` bits of `s` (the rest is left for the next number).
def Bits.read(n: Nat, s: String) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      Some{WNil{}}
    case 1n+p:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          Bits.cons(p, Bits.bit(c), Bits.read(p, t))

# `s` without its first `n` characters.
def Bits.drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{_, t}:
          Bits.drop(p, t)

def U32.bits(x: U32, rest: String) -> String:
  match x:
    case U32{w}:
      Bits.show(32n, w, rest)

def U32.of_word(m: Maybe<&2, Word(32n)>) -> Maybe<&2, U32>:
  match m:
    case Some{w}:
      Some{U32{w}}
    case None{}:
      None{}

def U32.of_bits(s: String) -> Maybe<&2, U32>:
  U32.of_word(Bits.read(32n, s))

def Invite.encode(i: Invite) -> String:
  match i:
    case Invite{r}:
      U32.bits(r, SNil{})

def Invite.of(m: Maybe<&2, U32>) -> Maybe<Invite>:
  match m:
    case Some{n}:
      Some{Invite{n}}
    case None{}:
      None{}

def Invite.decode(s: String) -> Maybe<Invite>:
  Invite.of(U32.of_bits(s))

type Message is Data:
  Played{move: Action}
  Resign{}

# "P" and the card, from and to squares as 32 bits each; "R" to resign.
def Message.encode(m: Message) -> String:
  match m:
    case Played{Action{c, f, t}}:
      SCon{'P', U32.bits(c, U32.bits(Cell.u32(f), U32.bits(Cell.u32(t), SNil{})))}
    case Resign{}:
      SCon{'R', SNil{}}

def Message.played(a: Maybe<&2, U32>, b: Maybe<&2, Cell>, c: Maybe<&2, Cell>) -> Maybe<Message>:
  match a b c:
    case Some{x} Some{y} Some{z}:
      Some{Played{Action{x, y, z}}}
    case _ _ _:
      None{}

def Cell.of_maybe(m: Maybe<&2, U32>) -> Maybe<&2, Cell>:
  match m:
    case Some{x}:
      Cell.of_u32(x)
    case None{}:
      None{}

def Message.parse(+body: String) -> Maybe<Message>:
  +rest = Bits.drop(32n, body)
  Message.played(U32.of_bits(body), Cell.of_maybe(U32.of_bits(rest)), Cell.of_maybe(U32.of_bits(Bits.drop(32n, rest))))

def Message.decode.resign(t: String) -> Maybe<Message>:
  match t:
    case SNil{}:
      Some{Resign{}}
    case _:
      None{}

def Message.decode.go(p: Bool, r: Bool, t: String) -> Maybe<Message>:
  match p r:
    case True{} _:
      Message.parse(t)
    case False{} True{}:
      Message.decode.resign(t)
    case False{} False{}:
      None{}

def Message.decode(s: String) -> Maybe<Message>:
  match s:
    case SNil{}:
      None{}
    case SCon{+h, t}:
      Message.decode.go(Char.is_eq(h, 'P'), Char.is_eq(h, 'R'), t)

def Message.code(m: Maybe<Message>) -> U32:
  match m:
    case Some{Played{a}}:
      (Action.code(a) + 1 : U32)
    case Some{Resign{}}:
      4294967295
    case None{}:
      0

# ================================================================ match flow (what the page asks before acting)

# Why a game ended, so the page never guesses it.
# ts: union
type Ending is Data:
  Playing{}
  KeeperTaken{}
  ReachedGoal{}
  Repeated{}
  Stalled{}

def ending.win(gone: Bool) -> Ending:
  match gone:
    case True{}:
      KeeperTaken{}
    case False{}:
      ReachedGoal{}

def ending.draw(stalled: Bool) -> Ending:
  match stalled:
    case True{}:
      Stalled{}
    case False{}:
      Repeated{}

def ending.of(o: Outcome, +g: Game) -> Ending:
  match o:
    case Ongoing{}:
      Playing{}
    case Winner{s}:
      ending.win(Cell.none(Pieces.teacher_of(Game.pieces(g), Side.other(s))))
    case Draw{}:
      ending.draw(Nat.is_ge(Game.quiet(g), 20n))

def ending(+g: Game) -> Ending:
  ending.of(Game.result(g), g)

def Ending.is_over(e: Ending) -> Bool:
  match e:
    case Playing{}:
      False{}
    case _:
      True{}

# What a tap on square `sq` does, given the card picked (none: any number not in the deck)
# and the button selected (none: NONE()).
# ts: union
type Click is Data:
  Play{card: U32, from: U32, to: U32}
  Select{sq: U32}
  Clear{}
  Crowded{}

# The page's view of a move: the card and the two square numbers.
def Click.play(m: Action) -> Click:
  match m:
    case Action{c, f, t}:
      Play{c, Cell.u32(f), Cell.u32(t)}

# The move a card and two square numbers name (off-board numbers name the corner).
def Action.of_parts(card: U32, +from: U32, +to: U32) -> Action:
  Action{card, Cell.or_corner(Cell.of_u32(from)), Cell.or_corner(Cell.of_u32(to))}

def Actions.keep(c: Bool, +m: Action, rest: List<&2, Action>) -> List<&2, Action>:
  match c:
    case True{}:
      m <> rest
    case False{}:
      rest

def Actions.with_card(xs: List<&2, Action>, +card: U32) -> List<&2, Action>:
  match xs:
    case Nil{}:
      []
    case Con{+m, rest}:
      Actions.keep(U32.is_eq(Action.card(m), card), m, Actions.with_card(rest, card))

def Actions.with_to(xs: List<&2, Action>, +to: Cell) -> List<&2, Action>:
  match xs:
    case Nil{}:
      []
    case Con{+m, rest}:
      Actions.keep(Cell.eq(to_of(m), to), m, Actions.with_to(rest, to))

def Actions.with_from(xs: List<&2, Action>, +from: Maybe<&2, Cell>) -> List<&2, Action>:
  match xs:
    case Nil{}:
      []
    case Con{+m, rest}:
      Actions.keep(Cell.is(from, Action.from(m)), m, Actions.with_from(rest, from))

def click.moves(mine: Bool, +g: Game) -> List<&2, Action>:
  match mine:
    case True{}:
      legal_moves(g)
    case False{}:
      []

def click.select(mine: Bool, same: Bool, +sq: Cell) -> Click:
  match mine same:
    case True{} False{}:
      Select{Cell.u32(sq)}
    case True{} True{}:
      Clear{}
    case False{} _:
      Clear{}

def click.crowd(mine: Bool, +sq: Cell) -> Click:
  match mine:
    case True{}:
      Select{Cell.u32(sq)}
    case False{}:
      Crowded{}

def click.one(rest: List<&2, Action>, +m: Action, +mine: Bool, +sq: Cell) -> Click:
  match rest:
    case Nil{}:
      Click.play(m)
    case Con{_, _}:
      click.crowd(mine, sq)

def click.reach(reach: List<&2, Action>, +mine: Bool, +sq: Cell) -> Click:
  match reach:
    case Nil{}:
      click.select(mine, False{}, sq)
    case Con{+m, rest}:
      click.one(rest, m, mine, sq)

def click.free(none: Bool, +reach: List<&2, Action>, +mine: Bool, +same: Bool, +sq: Cell) -> Click:
  match none:
    case True{}:
      click.reach(reach, mine, sq)
    case False{}:
      click.select(mine, same, sq)

def click.go(hit: List<&2, Action>, +none: Bool, +reach: List<&2, Action>, +mine: Bool, +same: Bool, +sq: Cell) -> Click:
  match hit:
    case Con{+m, _}:
      Click.play(m)
    case Nil{}:
      click.free(none, reach, mine, same, sq)

# A tapped dot that only one button reaches plays that button; a dot several buttons reach asks
# which one; tapping your own button selects it (again: lets it go).
# which one; tapping your own button selects it (again: lets it go).
def click(+g: Game, +me: Side, +card: U32, +s: Maybe<&2, Cell>, +sq: Cell) -> Click:
  +moves = Actions.with_card(click.moves(Side.same(Game.turn(g), me), g), card)
  +reach = Actions.with_to(moves, sq)
  +hit = Actions.with_from(reach, s)
  click.go(hit, Cell.none(s), reach, Pieces.side_at(Game.pieces(g), sq, me), Cell.is(s, sq), sq)

# The same, with the page's square numbers (49: none); a tap off the board selects nothing.
def click.api(at: Maybe<&2, Cell>, +g: Game, +me: Side, +card: U32, +s: U32) -> Click:
  match at:
    case None{}:
      Clear{}
    case Some{sq}:
      click(g, me, card, Cell.of_u32(s), sq)

# For the laws: a tap only ever plays a legal move, and only on your own turn.
def click_ok.of(c: Click, +g: Game, +me: Side) -> Bool:
  match c:
    case Play{card, f, t}:
      Side.same(Game.turn(g), me) && is_legal(g, Action.of_parts(card, f, t))
    case _:
      True{}

def click_ok(+g: Game, +me: Side, +card: U32, +s: U32, +sq: U32) -> Bool:
  click_ok.of(click.api(Cell.of_u32(sq), g, me, card, s), g, me)

# ================================================================ what the table shows

# The table draws exactly this list, rebuilt from the board every time: one token per piece,
# nothing remembered from an earlier move or game.
type Token is Data:
  Token{side: Side, keeper: Bool, cell: Cell}

def scene.of(ps: List<&2, Piece>) -> List<&2, Token>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{Piece{s, t, q}, rest}:
      Token{s, t, q} <> scene.of(rest)

def scene(g: Game) -> List<&2, Token>:
  scene.of(Game.pieces(g))

# What the table shows on `sq` (same codes as Pieces.code_at: 0 nothing).
def Tokens.code_at(ts: List<&2, Token>, +sq: Cell) -> U32:
  match ts:
    case Nil{}:
      0
    case Con{Token{s, t, q}, rest}:
      sel(Cell.eq(q, sq), Piece.code(s, t), Tokens.code_at(rest, sq))

def Tokens.len(ts: List<&2, Token>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Tokens.len(t)

def Tokens.count.add(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

# How many tokens of `side` the table shows.
def Tokens.count(ts: List<&2, Token>, +side: Side) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{Token{s, _, _}, rest}:
      Tokens.count.add(Side.same(s, side), Tokens.count(rest, side))

def Tokens.cells(ts: List<&2, Token>) -> List<&2, Cell>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Token{_, _, q}, rest}:
      q <> Tokens.cells(rest)

# No two tokens on the same square.
def Cells.unstacked(cs: List<&2, Cell>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(Cells.has(t, h)), Cells.unstacked(t))

def Tokens.nth(ts: List<&2, Token>, n: Nat) -> Token:
  match ts n:
    case Nil{} _:
      Token{Blue{}, False{}, Cell{F0{}, F0{}}}
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      Tokens.nth(t, p)

def Token.pack(t: Token) -> U32:
  match t:
    case Token{s, k, q}:
      (Piece.code(s, k) * 64 + Cell.u32(q) : U32)

# ================================================================ online protocol
# Two browsers deal and play with no dealer (app/src/net/online.ts). The cryptography runs in the
# page and is assumed sound: a hash binds its value, and a card locked by both players opens only
# with both keys. What to accept, what to reveal and which keys to hand over is decided here.

def Nats.has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Nat.is_eq(h, x) || Nats.has(t, x)

def Nats.keep(drop: Bool, h: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

# `xs` without any `x`.
def Nats.without(xs: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Nats.keep(Nat.is_eq(h, x), h, Nats.without(t, x))

def Nats.nth(xs: List<&2, Nat>, n: Nat) -> Nat:
  match xs n:
    case Nil{} _:
      99n
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      Nats.nth(t, p)

# The five dealt positions: blue (who created the room) holds 0 and 1, red 2 and 3, 4 is the table.
def Proto.mine(host: Bool) -> List<&2, Nat>:
  match host:
    case True{}:
      [0n, 1n]
    case False{}:
      [2n, 3n]

# At the deal each player hands over the keys of the other player's cards and of the table card.
def Proto.handed(host: Bool) -> List<&2, Nat>:
  match host:
    case True{}:
      [2n, 3n, 4n]
    case False{}:
      [0n, 1n, 4n]

# ---- the order of the messages

# Message kinds: 1 commit, 2 reveal (the coin), 3 d1, 4 d2, 5 d3, 6 d4 (the shuffle), 7 keys,
# 8 move, 9 resign. Anything else is 0.
# The setup messages each player receives, in order. Blue (the host) shuffles first.
def Proto.plan(host: Bool) -> List<&2, U32>:
  match host:
    case True{}:
      [1, 2, 4, 6, 7]
    case False{}:
      [1, 2, 3, 5, 7]

# The setup message expected at step `i` (99 once the deal is done).
def Proto.expected(host: Bool, i: Nat) -> U32:
  U32s.nth(Proto.plan(host), i)

def Proto.index.pick(hit: Bool, rest: Nat) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      Nat.add(rest, 1n)

# Where kind `k` sits in the plan (99 or more if it is not there).
def Proto.index(xs: List<&2, U32>, +k: U32) -> Nat:
  match xs:
    case Nil{}:
      99n
    case Con{h, t}:
      Proto.index.pick(U32.is_eq(h, k), Proto.index(t, k))

# ts: union
type Order is Data:
  Take{}
  Hold{}
  Cheat{}

def Order.is_cheat(o: Order) -> Bool:
  match o:
    case Cheat{}:
      True{}
    case _:
      False{}

def Proto.order.of(c: Cmp) -> Order:
  match c:
    case EQ{}:
      Take{}
    case GT{}:
      Hold{}
    case LT{}:
      Cheat{}

def Proto.order.planned(known: Bool, +j: Nat, +i: Nat) -> Order:
  match known:
    case True{}:
      Proto.order.of(Nat.cmp(j, i))
    case False{}:
      Cheat{}

# A setup kind not in my plan is never mine to receive.
def Proto.order.setup(+j: Nat, +i: Nat) -> Order:
  Proto.order.planned(Nat.is_lt(j, 5n), j, i)

def Proto.order.move(playing: Bool) -> Order:
  match playing:
    case True{}:
      Take{}
    case False{}:
      Cheat{}

def Proto.order.go(move: Bool, resign: Bool, +host: Bool, +i: Nat, +k: U32) -> Order:
  match move resign:
    case True{} _:
      Proto.order.move(Nat.is_ge(i, 5n))
    case False{} True{}:
      Take{}
    case False{} False{}:
      Proto.order.setup(Proto.index(Proto.plan(host), k), i)

# What to do with a message of kind `k` at setup step `i` (5 once the deal is done): take it now,
# hold it until its turn, or call it cheating (a repeated or late setup message, a message meant
# for the other player, or a move before the deal is done). Resigning is always taken.
def Proto.order(+host: Bool, +i: Nat, +k: U32) -> Order:
  Proto.order.go(U32.is_eq(k, 8), U32.is_eq(k, 9), host, i, k)

# The coin is accepted only when its hash matches the commitment and it is 0 or 1.
def Proto.coin_ok(matches: Bool, +bit: U32) -> Bool:
  Bool.and(matches, Bool.or(U32.is_eq(bit, 0), U32.is_eq(bit, 1)))

# ---- the other player's hand, as I can know it

# Positions they still hold hidden, cards of theirs everyone has seen (taken from the table), and
# the table card.
type Opp is Data:
  Opp{hidden: List<&2, Nat>, seen: List<&2, U32>, table: U32}

# What comes with a card they play: nothing, or the position a key was sent for and the card the
# page found under that position with it (99 if none).
type Proof is Data:
  NoProof{}
  Opened{pos: Nat, card: U32}

# ts: union
type Verdict is Data:
  Accepted{opp: Opp}
  Rejected{reason: U32}

def Opp.start(host: Bool, +table: U32) -> Opp:
  Opp{Proto.mine(Bool.not(host)), [], table}

def Opp.hidden(o: Opp) -> List<&2, Nat>:
  match o:
    case Opp{h, _, _}:
      h

def Opp.seen(o: Opp) -> List<&2, U32>:
  match o:
    case Opp{_, s, _}:
      s

def Opp.table(o: Opp) -> U32:
  match o:
    case Opp{_, _, t}:
      t

def Opp.check(ok: Bool, +pos: Nat, hid: List<&2, Nat>, seen: List<&2, U32>, +tb: U32, +c: U32) -> Verdict:
  match ok:
    case True{}:
      Accepted{Opp{Nats.without(hid, pos), tb <> seen, c}}
    case False{}:
      Rejected{2}

def Opp.proof(p: Proof, +hid: List<&2, Nat>, seen: List<&2, U32>, +tb: U32, +c: U32) -> Verdict:
  match p:
    case NoProof{}:
      Rejected{1}
    case Opened{+pos, opened}:
      Opp.check(Nats.has(hid, pos) && U32.is_eq(opened, c), pos, hid, seen, tb, c)

def Opp.play.go(known: Bool, hid: List<&2, Nat>, +seen: List<&2, U32>, +tb: U32, +c: U32, p: Proof) -> Verdict:
  match known:
    case True{}:
      Accepted{Opp{hid, tb <> U32s.remove(seen, c), c}}
    case False{}:
      Opp.proof(p, hid, seen, tb, c)

# They play card `c`: a card everyone has seen needs no proof; any other card needs a key that
# opens exactly that card at a position they still hold hidden. Rejected 1: no proof; 2: bad proof.
def Opp.play(o: Opp, +c: U32, p: Proof) -> Verdict:
  match o:
    case Opp{hid, +seen, tb}:
      Opp.play.go(U32s.has(seen, c), hid, seen, tb, c, p)

# I play a card: it goes to the table (the old table card comes to my hand, not theirs).
def Opp.i_played(o: Opp, +c: U32) -> Opp:
  match o:
    case Opp{hid, seen, _}:
      Opp{hid, seen, c}

def Verdict.ok(v: Verdict) -> Bool:
  match v:
    case Accepted{_}:
      True{}
    case Rejected{_}:
      False{}

def Verdict.opp(v: Verdict, +d: Opp) -> Opp:
  match v:
    case Accepted{o}:
      o
    case Rejected{_}:
      d

# ---- my own hidden cards: which position (and so which key) proves each one

type Held is Data:
  Held{card: U32, pos: Nat}

def Mine.start(host: Bool, +c0: U32, +c1: U32) -> List<&2, Held>:
  match host:
    case True{}:
      [Held{c0, 0n}, Held{c1, 1n}]
    case False{}:
      [Held{c0, 2n}, Held{c1, 3n}]

def Mine.pos.pick(hit: Bool, p: Nat, rest: Nat) -> Nat:
  match hit:
    case True{}:
      p
    case False{}:
      rest

# The position whose key proves `c` (99 if `c` is not one of my hidden cards).
def Mine.pos(hs: List<&2, Held>, +c: U32) -> Nat:
  match hs:
    case Nil{}:
      99n
    case Con{Held{hc, p}, t}:
      Mine.pos.pick(U32.is_eq(hc, c), p, Mine.pos(t, c))

def Mine.keep(drop: Bool, h: Held, rest: List<&2, Held>) -> List<&2, Held>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

# After playing `c` it is no longer hidden: its key is never sent again.
def Mine.play(hs: List<&2, Held>, +c: U32) -> List<&2, Held>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Held{+hc, +p}, t}:
      Mine.keep(U32.is_eq(hc, c), Held{hc, p}, Mine.play(t, c))

# ================================================================ API for the web page (numbers in, numbers out)

def api_new(blue_key: U32, red_key: U32) -> Game:
  start(Setup{Secret.of_key(blue_key), Secret.of_key(red_key)})

# Online the cards come from the cryptographic draw; 99 marks a card we cannot see.
def api_new_dealt(starter: U32, b0: U32, b1: U32, r0: U32, r1: U32, t: U32) -> Game:
  start_dealt(Side.of_code(starter), Deal{[b0, b1], [r0, r1], t})

# Online: who starts, from both players' coins (0 or 1, exchanged with commitments).
def api_starter(blue_coin: U32, red_coin: U32) -> U32:
  Side.code(Coin.side(U32.is_zero(blue_coin), U32.is_zero(red_coin)))

def code_at.checked(at: Maybe<&2, Cell>, g: Game) -> U32:
  match at:
    case Some{sq}:
      Pieces.code_at(Game.pieces(g), sq)
    case None{}:
      0

def api_cell(g: Game, sq: U32) -> U32:
  code_at.checked(Cell.of_u32(sq), g)

def api_hand(g: Game, side: U32, i: U32) -> U32:
  U32s.nth(Game.hand(g, Side.of_code(side)), U32.to_nat(i))

def api_table(g: Game) -> U32:
  Game.table(g)

def api_turn(g: Game) -> U32:
  Side.code(Game.turn(g))

def api_outcome(g: Game) -> U32:
  Outcome.code(Game.result(g))

def api_quiet(g: Game) -> U32:
  U32.from_nat(Game.quiet(g))

def api_move_count(+g: Game) -> U32:
  U32.from_nat(Actions.len(legal_moves(g)))

def api_move(+g: Game, i: U32) -> U32:
  Action.code(Actions.nth(legal_moves(g), U32.to_nat(i)))

def is_legal.checked(ok: Bool, +g: Game, +code: U32) -> U32:
  match ok:
    case True{}:
      sel(is_legal(g, Action.of_code(code)), 1, 0)
    case False{}:
      0

def api_is_legal(+g: Game, +code: U32) -> U32:
  is_legal.checked(Action.valid_code(code), g, code)

def play.checked(ok: Bool, +g: Game, +code: U32) -> Game:
  match ok:
    case True{}:
      play(g, Action.of_code(code))
    case False{}:
      g

def api_play(+g: Game, +code: U32) -> Game:
  play.checked(Action.valid_code(code), g, code)

def play_revealed.checked(ok: Bool, +g: Game, +code: U32) -> Game:
  match ok:
    case True{}:
      play_revealed(g, Action.of_code(code))
    case False{}:
      g

def api_play_revealed(+g: Game, +code: U32) -> Game:
  play_revealed.checked(Action.valid_code(code), g, code)

def api_bot(+g: Game, level: U32, seed: U32) -> U32:
  Action.code(bot.decide(view(g, Game.turn(g)), U32.to_nat(level), (seed + 1 : U32)))

# Chances seen by `viewer`, packed as blue * 1000000 + red * 1000 + draws (out of 100).
def Chances.pack(c: Chances) -> U32:
  match c:
    case Chances{b, r, d, _}:
      (U32.from_nat(b) * 1000000 + U32.from_nat(r) * 1000 + U32.from_nat(d) : U32)

def api_chances(g: Game, viewer: U32) -> U32:
  Chances.pack(chances(view(g, Side.of_code(viewer))))

def api_card_step_count(id: U32) -> U32:
  U32.from_nat(Steps.len(card_steps(id)))

# One step of a card for drawing it: (dx + 3) * 8 + (dy + 3), dx > 0 right, dy > 0 forward.
def api_card_step(id: U32, i: U32) -> U32:
  Step.pack(Steps.nth(card_steps(id), U32.to_nat(i)))

# Messages between players go through these, so the roundtrip law covers what is sent.
def api_msg_move(code: U32) -> String:
  Message.encode(Played{Action.of_code(code)})

def api_msg_resign() -> String:
  Message.encode(Resign{})

# 0 = not a message, 4294967295 = resign, otherwise the move code + 1.
def api_msg_read(s: String) -> U32:
  Message.code(Message.decode(s))

def api_invite(room: U32) -> String:
  Invite.encode(Invite{room})

def Cards.name_of.pick(hit: Bool, a: String, b: String) -> String:
  match hit:
    case True{}:
      a
    case False{}:
      b

def Cards.name_of(cs: List<&2, Card>, +id: U32) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{Card{cid, n, _}, t}:
      Cards.name_of.pick(U32.is_eq(cid, id), n, Cards.name_of(t, id))

def api_card_name(id: U32) -> String:
  Cards.name_of(deck(), id)

# ---- "this card never traps anyone": checked by the checker itself (see LAWS.bend)

def Reach.add.go(skip: Bool, c: Cell, acc: List<&2, Cell>) -> List<&2, Cell>:
  match skip:
    case True{}:
      acc
    case False{}:
      c <> acc

def Reach.add(t: Maybe<&2, Cell>, +acc: List<&2, Cell>) -> List<&2, Cell>:
  match t:
    case None{}:
      acc
    case Some{+c}:
      Reach.add.go(Cells.has(acc, c), c, acc)

def Reach.targets(sts: List<&2, Step>, +sq: Cell, +side: Side, acc: List<&2, Cell>) -> List<&2, Cell>:
  match sts:
    case Nil{}:
      acc
    case Con{st, rest}:
      Reach.targets(rest, sq, side, Reach.add(Step.target(st, sq, side), acc))



# Squares reachable from the queue with the card's steps, explored one square at a time and
# stopping as soon as 8 are known (that is all the argument needs).
# stopping as soon as 8 are known (that is all the argument needs).
def Reach.walk(fuel: Nat, enough: Bool, queue: List<&2, Cell>, +sts: List<&2, Step>, +side: Side, +seen: List<&2, Cell>) -> List<&2, Cell>:
  match fuel enough queue:
    case 0n _ _:
      seen
    case 1n+f True{} _:
      seen
    case 1n+f False{} Nil{}:
      seen
    case 1n+f False{} Con{sq, rest}:
      +fresh = Reach.targets(sts, sq, side, seen)
      +new = Cells.take(Nat.sub(Cells.len(fresh), Cells.len(seen)), fresh)
      Reach.walk(f, Nat.is_ge(Cells.len(fresh), 8n), Cells.append(rest, new), sts, side, fresh)

# The argument, for one card: if every piece of a side were stuck, the set of their squares would be
# closed under the card's steps (each step leaves the board or lands on one of them). A closed set
# holding a square holds everything reachable from it, and from every square at least 8 squares
# are reachable, so it would take 8 pieces: one side has at most 7.
# closed under the card's steps (each step leaves the board or lands on one of them). A closed set
# holding a square holds everything reachable from it, and from every square at least 8 squares
# are reachable, so it would take 8 pieces: one side has at most 7. (Red sees the board turned around.)
def Card.never_traps.go(sqs: List<&2, Cell>, +sts: List<&2, Step>, +side: Side) -> Bool:
  match sqs:
    case Nil{}:
      True{}
    case Con{+sq, rest}:
      Nat.is_ge(Cells.len(Reach.walk(49n, False{}, [sq], sts, side, [sq])), 8n) && Card.never_traps.go(rest, sts, side)

def Cards.never_trap(cs: List<&2, Card>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{Card{_, _, +st}, t}:
      Card.never_traps.go(Cells.all(), st, Blue{}) && Card.never_traps.go(Cells.all(), st, Red{}) && Cards.never_trap(t)

def deck_never_traps() -> Bool:
  Cards.never_trap(deck())

def api_deck_never_traps() -> U32:
  sel(deck_never_traps(), 1, 0)

def api_width() -> U32:
  W()

def api_home(side: U32) -> U32:
  Cell.u32(Side.home(Side.of_code(side)))

def api_move_card(code: U32) -> U32:
  Action.card(Action.of_code(code))

def api_move_from(code: U32) -> U32:
  Cell.u32(Action.from(Action.of_code(code)))

def api_move_to(code: U32) -> U32:
  Cell.u32(to_of(Action.of_code(code)))

# How the game stands, as a value TS can switch on (o.$ is "Ongoing", "Winner" or "Draw").
def api_outcome_of(g: Game) -> Outcome:
  Game.result(g)

# The chances `viewer` sees, as a record TS can read.
def api_chances_of(g: Game, viewer: U32) -> Chances:
  chances(view(g, Side.of_code(viewer)))

# Why the game ended (e.$ is "Playing", "KeeperTaken", "ReachedGoal", "Repeated" or "Stalled").
def api_ending(+g: Game) -> Ending:
  ending(g)

# What tapping `sq` does for `me` with card `card` picked (99: none) and button `s` selected (49: none).
def api_click(+g: Game, me: U32, card: U32, s: U32, +sq: U32) -> Click:
  click.api(Cell.of_u32(sq), g, Side.of_code(me), card, s)

# A tap's move, played as the page received it (the tap law covers exactly this move).
def api_play_move(+g: Game, card: U32, from: U32, to: U32) -> Game:
  play(g, Action.of_parts(card, from, to))

def api_move_code(card: U32, from: U32, to: U32) -> U32:
  Action.code(Action.of_parts(card, from, to))

# The table's tokens: api_token(g, i) = piece code * 64 + square (codes as api_cell).
def api_token_count(+g: Game) -> U32:
  U32.from_nat(Tokens.len(scene(g)))

def api_token(+g: Game, i: U32) -> U32:
  Token.pack(Tokens.nth(scene(g), U32.to_nat(i)))

# ---- online protocol, for app/src/net/online.ts (host: 1 for blue, 0 for red; 99 = none)

def api_proto_mine(host: U32, i: U32) -> U32:
  U32.from_nat(Nats.nth(Proto.mine(Bool.not(U32.is_zero(host))), U32.to_nat(i)))

def api_proto_handed(host: U32, i: U32) -> U32:
  U32.from_nat(Nats.nth(Proto.handed(Bool.not(U32.is_zero(host))), U32.to_nat(i)))

def api_opp_start(host: U32, table: U32) -> Opp:
  Opp.start(Bool.not(U32.is_zero(host)), table)

def Proof.of(has: Bool, +pos: U32, +card: U32) -> Proof:
  match has:
    case True{}:
      Opened{U32.to_nat(pos), card}
    case False{}:
      NoProof{}

# They play `card`, with or without a proof (`pos` and the card the page opened there).
def api_opp_play(o: Opp, card: U32, has_proof: U32, pos: U32, opened: U32) -> Verdict:
  Opp.play(o, card, Proof.of(Bool.not(U32.is_zero(has_proof)), pos, opened))

def api_opp_i_played(o: Opp, card: U32) -> Opp:
  Opp.i_played(o, card)

def api_mine_start(host: U32, c0: U32, c1: U32) -> List<&2, Held>:
  Mine.start(Bool.not(U32.is_zero(host)), c0, c1)

def api_mine_pos(hs: List<&2, Held>, card: U32) -> U32:
  U32.from_nat(Mine.pos(hs, card))

def api_mine_play(hs: List<&2, Held>, card: U32) -> List<&2, Held>:
  Mine.play(hs, card)

def api_proto_expected(host: U32, step: U32) -> U32:
  Proto.expected(Bool.not(U32.is_zero(host)), U32.to_nat(step))

def api_proto_order(host: U32, step: U32, kind: U32) -> Order:
  Proto.order(Bool.not(U32.is_zero(host)), U32.to_nat(step), kind)

def api_proto_coin_ok(matches: U32, bit: U32) -> U32:
  sel(Proto.coin_ok(Bool.not(U32.is_zero(matches)), bit), 1, 0)
