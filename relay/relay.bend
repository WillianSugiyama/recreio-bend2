import Base

# The relay of an online room: it pairs two browsers and forwards their messages. It understands
# nothing of the game and decides nothing about it; LAWS.bend states what it may and may not do.
# The Worker (src/index.js) only turns WebSocket events into `step` calls and sends the notes back.

# Who is in the room, in the order they came in (each browser has a random id).
type Seats is Data:
  Empty{}
  One{a: U32}
  Two{a: U32, b: U32}

type RoomEvent is Data:
  Enter{id: U32}
  Talk{from: U32, size: U32, text: String}
  Quit{id: U32}

# What the relay sends: a message to forward, "someone came" or "the other one left".
type Note is Data:
  Forward{to: U32, text: String}
  Joined{to: U32}
  Gone{to: U32}

# The room after an event, whether a joining browser was let in, and what to send.
type RStep is Data:
  RStep{seats: Seats, accepted: Bool, out: List<&2, Note>}

# The largest message forwarded (64 KB).
def MAX() -> U32:
  65536

def room.join.one(same: Bool, +a: U32, +id: U32) -> RStep:
  match same:
    case True{}:
      RStep{One{a}, False{}, []}
    case False{}:
      RStep{Two{a, id}, True{}, [Joined{a}, Joined{id}]}

def room.join(s: Seats, +id: U32) -> RStep:
  match s:
    case Empty{}:
      RStep{One{id}, True{}, []}
    case One{+a}:
      room.join.one(U32.is_eq(a, id), a, id)
    case Two{a, b}:
      RStep{Two{a, b}, False{}, []}

def room.forward.two(from_a: Bool, from_b: Bool, +a: U32, +b: U32, +text: String) -> List<&2, Note>:
  match from_a from_b:
    case True{} _:
      [Forward{b, text}]
    case False{} True{}:
      [Forward{a, text}]
    case False{} False{}:
      []

def room.forward(s: Seats, +from: U32, +text: String) -> List<&2, Note>:
  match s:
    case Two{+a, +b}:
      room.forward.two(U32.is_eq(from, a), U32.is_eq(from, b), a, b, text)
    case _:
      []

def room.say(fits: Bool, +s: Seats, +from: U32, +text: String) -> RStep:
  match fits:
    case True{}:
      RStep{s, True{}, room.forward(s, from, text)}
    case False{}:
      RStep{s, True{}, []}

def room.leave.two(is_a: Bool, is_b: Bool, +a: U32, +b: U32) -> RStep:
  match is_a is_b:
    case True{} _:
      RStep{One{b}, True{}, [Gone{b}]}
    case False{} True{}:
      RStep{One{a}, True{}, [Gone{a}]}
    case False{} False{}:
      RStep{Two{a, b}, True{}, []}

def room.leave.one(is_a: Bool, +a: U32) -> RStep:
  match is_a:
    case True{}:
      RStep{Empty{}, True{}, []}
    case False{}:
      RStep{One{a}, True{}, []}

def room.leave(s: Seats, +id: U32) -> RStep:
  match s:
    case Empty{}:
      RStep{Empty{}, True{}, []}
    case One{+a}:
      room.leave.one(U32.is_eq(id, a), a)
    case Two{+a, +b}:
      room.leave.two(U32.is_eq(id, a), U32.is_eq(id, b), a, b)

def step(+s: Seats, e: RoomEvent) -> RStep:
  match e:
    case Enter{id}:
      room.join(s, id)
    case Talk{from, size, text}:
      room.say((size <= MAX() : U32), s, from, text)
    case Quit{id}:
      room.leave(s, id)

def RStep.seats(t: RStep) -> Seats:
  match t:
    case RStep{s, _, _}:
      s

def RStep.out(t: RStep) -> List<&2, Note>:
  match t:
    case RStep{_, _, o}:
      o

# The room after a sequence of events, from an empty room.
def after.go(es: List<&2, RoomEvent>, +s: Seats) -> Seats:
  match es:
    case Nil{}:
      s
    case Con{e, rest}:
      after.go(rest, RStep.seats(step(s, e)))

def after(es: List<&2, RoomEvent>) -> Seats:
  after.go(es, Empty{})

# No browser holds both seats.
def Seats.distinct(s: Seats) -> Bool:
  match s:
    case Two{a, b}:
      Bool.not(U32.is_eq(a, b))
    case _:
      True{}

# ---------------------------------------------------------------- for the Worker (numbers in, numbers out)

def Seats.of(none: Bool, one: Bool, a: U32, b: U32) -> Seats:
  match none one:
    case True{} _:
      Empty{}
    case False{} True{}:
      One{a}
    case False{} False{}:
      Two{a, b}

def api_seats(+n: U32, a: U32, b: U32) -> Seats:
  Seats.of(U32.is_zero(n), U32.is_eq(n, 1), a, b)

def api_join(+s: Seats, id: U32) -> RStep:
  step(s, Enter{id})

def api_message(+s: Seats, from: U32, size: U32, text: String) -> RStep:
  step(s, Talk{from, size, text})

def api_close(+s: Seats, id: U32) -> RStep:
  step(s, Quit{id})

def api_accepted(t: RStep) -> U32:
  match t:
    case RStep{_, True{}, _}:
      1
    case RStep{_, False{}, _}:
      0

def Notes.len(ns: List<&2, Note>) -> U32:
  match ns:
    case Nil{}:
      0
    case Con{_, t}:
      (1 + Notes.len(t) : U32)

def Notes.nth(ns: List<&2, Note>, n: Nat) -> Note:
  match ns n:
    case Nil{} _:
      Gone{0}
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      Notes.nth(t, p)

def api_note_count(t: RStep) -> U32:
  Notes.len(RStep.out(t))

# A note: its kind (0 forward, 1 someone joined, 2 the other one left) and who receives it.
def Note.kind(n: Note) -> U32:
  match n:
    case Forward{_, _}:
      0
    case Joined{_}:
      1
    case Gone{_}:
      2

def Note.to(n: Note) -> U32:
  match n:
    case Forward{to, _}:
      to
    case Joined{to}:
      to
    case Gone{to}:
      to

def api_note_kind(t: RStep, i: U32) -> U32:
  Note.kind(Notes.nth(RStep.out(t), U32.to_nat(i)))

def api_note_to(t: RStep, i: U32) -> U32:
  Note.to(Notes.nth(RStep.out(t), U32.to_nat(i)))
