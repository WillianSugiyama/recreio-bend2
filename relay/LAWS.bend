import Base
import ./relay.bend as R

# Como ler uma lei: veja o LAWS.bend do jogo. Aqui, "a" e "b" são os dois navegadores da sala
# (na ordem em que entraram) e R.step é o que o relay faz com cada acontecimento.

# ============ ENTRAR NA SALA ============

# O primeiro a entrar espera sozinho; ninguém recebe nada.
law first_one_waits:
  for id: U32
  {R.step(R.Empty{}, R.Enter{id}) == R.RStep{R.One{id}, True{}, []} : R.RStep}

# Quando entra o segundo, os dois ficam sabendo.
law second_one_starts:
  for +a: U32
  for +id: U32
  for other: {U32.is_eq(a, id) == False{} : Bool}
  {R.step(R.One{a}, R.Enter{id}) == R.RStep{R.Two{a, id}, True{}, [R.Joined{a}, R.Joined{id}]} : R.RStep}

# Um terceiro é recusado, e a sala continua igual.
law third_one_refused:
  for +a: U32
  for +b: U32
  for id: U32
  {R.step(R.Two{a, b}, R.Enter{id}) == R.RStep{R.Two{a, b}, False{}, []} : R.RStep}

# Um mesmo navegador nunca ocupa os dois lugares.
law never_twice_in_the_room:
  for es: List<&2, R.RoomEvent>
  {R.Seats.distinct(R.after(es)) == True{} : Bool}

# ============ MENSAGENS ============

# A mensagem de "a" chega só a "b", exatamente como foi enviada (até 64 KB).
law first_reaches_only_second:
  for +a: U32
  for +b: U32
  for distinct: {U32.is_eq(a, b) == False{} : Bool}
  for +size: U32
  for fits: {(size <= R.MAX() : U32) == True{} : Bool}
  for text: String
  {R.RStep.out(R.step(R.Two{a, b}, R.Talk{a, size, text})) == [R.Forward{b, text}] : List<&2, R.Note>}

# E a de "b" chega só a "a".
law second_reaches_only_first:
  for +a: U32
  for +b: U32
  for distinct: {U32.is_eq(a, b) == False{} : Bool}
  for +size: U32
  for fits: {(size <= R.MAX() : U32) == True{} : Bool}
  for text: String
  {R.RStep.out(R.step(R.Two{a, b}, R.Talk{b, size, text})) == [R.Forward{a, text}] : List<&2, R.Note>}

# Quem não está na sala não fala com ninguém.
law stranger_is_ignored:
  for +a: U32
  for +b: U32
  for +from: U32
  for not_a: {U32.is_eq(from, a) == False{} : Bool}
  for not_b: {U32.is_eq(from, b) == False{} : Bool}
  for size: U32
  for text: String
  {R.RStep.out(R.step(R.Two{a, b}, R.Talk{from, size, text})) == [] : List<&2, R.Note>}

# Sozinho na sala, a mensagem não vai para ninguém (nem volta para quem mandou).
law alone_nobody_hears:
  for a: U32
  for from: U32
  for size: U32
  for text: String
  {R.RStep.out(R.step(R.One{a}, R.Talk{from, size, text})) == [] : List<&2, R.Note>}

# Mensagem maior que 64 KB não é repassada.
law too_big_is_dropped:
  for s: R.Seats
  for from: U32
  for +size: U32
  for big: {(size <= R.MAX() : U32) == False{} : Bool}
  for text: String
  {R.RStep.out(R.step(s, R.Talk{from, size, text})) == [] : List<&2, R.Note>}

# ============ SAIR ============

# Quando "a" sai, "b" fica sabendo e passa a esperar sozinho.
law first_leaves_second_hears:
  for +a: U32
  for +b: U32
  {R.step(R.Two{a, b}, R.Quit{a}) == R.RStep{R.One{b}, True{}, [R.Gone{b}]} : R.RStep}

# Quando "b" sai, "a" fica sabendo.
law second_leaves_first_hears:
  for +a: U32
  for +b: U32
  for distinct: {U32.is_eq(a, b) == False{} : Bool}
  {R.step(R.Two{a, b}, R.Quit{b}) == R.RStep{R.One{a}, True{}, [R.Gone{a}]} : R.RStep}
