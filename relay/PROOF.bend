import Base
import ./relay.bend as R
import ./LAWS.bend as Laws

# Proofs of the relay's laws. The number lemmas are copied from the game's PROOF.bend.

def L.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def L.false_is_not_true(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : L.disc(_)
  Unit{}

def L.tnf(+h: {True{} == False{} : Bool}) -> Empty:
  L.false_is_not_true(Equal.sym(Bool, True{}, False{}, h))

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

def L.u32_eq_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, L.word_cmp_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

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

def L.u32_eq_true(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %L.word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

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

# ---------------------------------------------------------------- entering

def Laws.first_one_waits(id):
  {==}

def Laws.second_one_starts(a, id, other):
  %Equal.sym(Bool, U32.is_eq(a, id), False{}, other) : {R.room.join.one(_, a, id) == R.RStep{R.Two{a, id}, True{}, [R.Joined{a}, R.Joined{id}]} : R.RStep}
  {==}

def Laws.third_one_refused(a, b, id):
  {==}

def L.join_keeps.go(+a: U32, +id: U32, +b: Bool, +e: {U32.is_eq(a, id) == b : Bool}) -> {R.Seats.distinct(R.RStep.seats(R.room.join.one(U32.is_eq(a, id), a, id))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(a, id), True{}, e) : {R.Seats.distinct(R.RStep.seats(R.room.join.one(_, a, id))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(a, id), False{}, e) : {R.Seats.distinct(R.RStep.seats(R.room.join.one(_, a, id))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(a, id), False{}, e) : {Bool.not(_) == True{} : Bool}
      {==}

def L.leave_two.go(+a: U32, +b: U32, +id: U32, +x: Bool, +ex: {U32.is_eq(id, a) == x : Bool}, +y: Bool, +ey: {U32.is_eq(id, b) == y : Bool}, +h: {Bool.not(U32.is_eq(a, b)) == True{} : Bool}) -> {R.Seats.distinct(R.RStep.seats(R.room.leave.two(U32.is_eq(id, a), U32.is_eq(id, b), a, b))) == True{} : Bool}:
  match x y:
    case True{} _:
      %Equal.sym(Bool, U32.is_eq(id, a), True{}, ex) : {R.Seats.distinct(R.RStep.seats(R.room.leave.two(_, U32.is_eq(id, b), a, b))) == True{} : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, U32.is_eq(id, a), False{}, ex) : {R.Seats.distinct(R.RStep.seats(R.room.leave.two(_, U32.is_eq(id, b), a, b))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(id, b), True{}, ey) : {R.Seats.distinct(R.RStep.seats(R.room.leave.two(False{}, _, a, b))) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, U32.is_eq(id, a), False{}, ex) : {R.Seats.distinct(R.RStep.seats(R.room.leave.two(_, U32.is_eq(id, b), a, b))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(id, b), False{}, ey) : {R.Seats.distinct(R.RStep.seats(R.room.leave.two(False{}, _, a, b))) == True{} : Bool}
      h

def L.leave_one.go(+a: U32, +id: U32, +x: Bool, +ex: {U32.is_eq(id, a) == x : Bool}) -> {R.Seats.distinct(R.RStep.seats(R.room.leave.one(U32.is_eq(id, a), a))) == True{} : Bool}:
  match x:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(id, a), True{}, ex) : {R.Seats.distinct(R.RStep.seats(R.room.leave.one(_, a))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(id, a), False{}, ex) : {R.Seats.distinct(R.RStep.seats(R.room.leave.one(_, a))) == True{} : Bool}
      {==}

def L.say_keeps(+f: Bool, +s: R.Seats, +from: U32, +text: String, +h: {R.Seats.distinct(s) == True{} : Bool}) -> {R.Seats.distinct(R.RStep.seats(R.room.say(f, s, from, text))) == True{} : Bool}:
  match f:
    case True{}:
      h
    case False{}:
      h

# Every event keeps the two seats apart.
def L.step_keeps(+s: R.Seats, +e: R.RoomEvent, +h: {R.Seats.distinct(s) == True{} : Bool}) -> {R.Seats.distinct(R.RStep.seats(R.step(s, e))) == True{} : Bool}:
  match s e:
    case R.Empty{} R.Enter{id}:
      {==}
    case R.One{a} R.Enter{id}:
      L.join_keeps.go(a, id, U32.is_eq(a, id), {==})
    case R.Two{a, b} R.Enter{id}:
      h
    case R.Empty{} R.Talk{from, size, text}:
      L.say_keeps((size <= R.MAX() : U32), R.Empty{}, from, text, h)
    case R.One{a} R.Talk{from, size, text}:
      L.say_keeps((size <= R.MAX() : U32), R.One{a}, from, text, h)
    case R.Two{a, b} R.Talk{from, size, text}:
      L.say_keeps((size <= R.MAX() : U32), R.Two{a, b}, from, text, h)
    case R.Empty{} R.Quit{id}:
      {==}
    case R.One{a} R.Quit{id}:
      L.leave_one.go(a, id, U32.is_eq(id, a), {==})
    case R.Two{a, b} R.Quit{id}:
      L.leave_two.go(a, b, id, U32.is_eq(id, a), {==}, U32.is_eq(id, b), {==}, h)

def L.after_keeps(+es: List<&2, R.RoomEvent>, +s: R.Seats, +h: {R.Seats.distinct(s) == True{} : Bool}) -> {R.Seats.distinct(R.after.go(es, s)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{e, rest}:
      L.after_keeps(rest, R.RStep.seats(R.step(s, e)), L.step_keeps(s, e, h))

def Laws.never_twice_in_the_room(es):
  L.after_keeps(es, R.Empty{}, {==})

# ---------------------------------------------------------------- messages

def Laws.first_reaches_only_second(a, b, distinct, size, fits, text):
  %Equal.sym(Bool, (size <= R.MAX() : U32), True{}, fits) : {R.RStep.out(R.room.say(_, R.Two{a, b}, a, text)) == [R.Forward{b, text}] : List<&2, R.Note>}
  %Equal.sym(Bool, U32.is_eq(a, a), True{}, L.u32_eq_refl(a)) : {R.room.forward.two(_, U32.is_eq(a, b), a, b, text) == [R.Forward{b, text}] : List<&2, R.Note>}
  {==}

def Laws.second_reaches_only_first(a, b, distinct, size, fits, text):
  +ba = Equal.trans(Bool, U32.is_eq(b, a), U32.is_eq(a, b), False{}, L.u32_eq_sym(b, a), distinct)
  %Equal.sym(Bool, (size <= R.MAX() : U32), True{}, fits) : {R.RStep.out(R.room.say(_, R.Two{a, b}, b, text)) == [R.Forward{a, text}] : List<&2, R.Note>}
  %Equal.sym(Bool, U32.is_eq(b, a), False{}, ba) : {R.room.forward.two(_, U32.is_eq(b, b), a, b, text) == [R.Forward{a, text}] : List<&2, R.Note>}
  %Equal.sym(Bool, U32.is_eq(b, b), True{}, L.u32_eq_refl(b)) : {R.room.forward.two(False{}, _, a, b, text) == [R.Forward{a, text}] : List<&2, R.Note>}
  {==}

def L.stranger.go(+f: Bool, +a: U32, +b: U32, +from: U32, +text: String, +not_a: {U32.is_eq(from, a) == False{} : Bool}, +not_b: {U32.is_eq(from, b) == False{} : Bool}) -> {R.RStep.out(R.room.say(f, R.Two{a, b}, from, text)) == [] : List<&2, R.Note>}:
  match f:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(from, a), False{}, not_a) : {R.room.forward.two(_, U32.is_eq(from, b), a, b, text) == [] : List<&2, R.Note>}
      %Equal.sym(Bool, U32.is_eq(from, b), False{}, not_b) : {R.room.forward.two(False{}, _, a, b, text) == [] : List<&2, R.Note>}
      {==}
    case False{}:
      {==}

def Laws.stranger_is_ignored(a, b, from, not_a, not_b, size, text):
  L.stranger.go((size <= R.MAX() : U32), a, b, from, text, not_a, not_b)

def L.alone.go(+f: Bool, +a: U32, +from: U32, +text: String) -> {R.RStep.out(R.room.say(f, R.One{a}, from, text)) == [] : List<&2, R.Note>}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.alone_nobody_hears(a, from, size, text):
  L.alone.go((size <= R.MAX() : U32), a, from, text)

def Laws.too_big_is_dropped(s, from, size, big, text):
  %Equal.sym(Bool, (size <= R.MAX() : U32), False{}, big) : {R.RStep.out(R.room.say(_, s, from, text)) == [] : List<&2, R.Note>}
  {==}

# ---------------------------------------------------------------- leaving

def Laws.first_leaves_second_hears(a, b):
  %Equal.sym(Bool, U32.is_eq(a, a), True{}, L.u32_eq_refl(a)) : {R.room.leave.two(_, U32.is_eq(a, b), a, b) == R.RStep{R.One{b}, True{}, [R.Gone{b}]} : R.RStep}
  {==}

def Laws.second_leaves_first_hears(a, b, distinct):
  +ba = Equal.trans(Bool, U32.is_eq(b, a), U32.is_eq(a, b), False{}, L.u32_eq_sym(b, a), distinct)
  %Equal.sym(Bool, U32.is_eq(b, a), False{}, ba) : {R.room.leave.two(_, U32.is_eq(b, b), a, b) == R.RStep{R.One{a}, True{}, [R.Gone{a}]} : R.RStep}
  %Equal.sym(Bool, U32.is_eq(b, b), True{}, L.u32_eq_refl(b)) : {R.room.leave.two(False{}, _, a, b) == R.RStep{R.One{a}, True{}, [R.Gone{a}]} : R.RStep}
  {==}
