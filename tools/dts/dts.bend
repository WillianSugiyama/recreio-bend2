import Base

# Writes TypeScript declarations for every `def api_*` of a Bend file. Numbers and strings map to
# TS; every other Bend type becomes an opaque branded value that TS can hold but not open.
# Text is handled as lists of characters (Bend strings are lists underneath anyway).

# ================================================================ characters

def Cs.lit(s: String) -> List<&2, Char>:
  String.to_list(s)

def Cs.eq(a: List<&2, Char>, b: List<&2, Char>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, t} Con{y, u}:
      Char.is_eq(x, y) && Cs.eq(t, u)
    case _ _:
      False{}

def Cs.starts(cs: List<&2, Char>, p: List<&2, Char>) -> Bool:
  match cs p:
    case _ Nil{}:
      True{}
    case Nil{} Con{_, _}:
      False{}
    case Con{x, t} Con{y, u}:
      Char.is_eq(x, y) && Cs.starts(t, u)

def Cs.reverse(cs: List<&2, Char>, acc: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      acc
    case Con{h, t}:
      Cs.reverse(t, h <> acc)

def Cs.drop(cs: List<&2, Char>, n: Nat) -> List<&2, Char>:
  match cs n:
    case _ 0n:
      cs
    case Nil{} _:
      Nil{}
    case Con{_, t} 1n+p:
      Cs.drop(t, p)

def Cs.before.go(hit: Bool, h: Char, rest: List<&2, Char>) -> List<&2, Char>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      h <> rest

# The characters before the first `stop` (all of them if there is none).
def Cs.before(cs: List<&2, Char>, +stop: Char) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Cs.before.go(Char.is_eq(h, stop), h, Cs.before(t, stop))

def Cs.after.go(hit: Bool, t: List<&2, Char>, rest: List<&2, Char>) -> List<&2, Char>:
  match hit:
    case True{}:
      t
    case False{}:
      rest

# The characters after the first `stop` (none if there is none).
def Cs.after(cs: List<&2, Char>, +stop: Char) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{h, +t}:
      Cs.after.go(Char.is_eq(h, stop), t, Cs.after(t, stop))

def Cs.trim_left.go(space: Bool, h: Char, t: List<&2, Char>, rest: List<&2, Char>) -> List<&2, Char>:
  match space:
    case True{}:
      rest
    case False{}:
      h <> t

def Cs.trim_left(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Cs.trim_left.go(Char.is_eq(h, ' '), h, t, Cs.trim_left(t))

def Cs.trim(cs: List<&2, Char>) -> List<&2, Char>:
  Cs.reverse(Cs.trim_left(Cs.reverse(Cs.trim_left(cs), Nil{})), Nil{})

def Cs.is_word_char(+c: Char) -> Bool:
  Char.is_upper(c) || Char.is_lower(c) || Char.is_digit(c)

def Cs.all_word(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Cs.is_word_char(h) && Cs.all_word(t)

# A plain type name: a capital letter, then letters and digits (so no generics like List<..>).
def Cs.is_type_name(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Char.is_upper(h) && Cs.all_word(t)

def Cs.strip_sigil.go(sigil: Bool, h: Char, t: List<&2, Char>) -> List<&2, Char>:
  match sigil:
    case True{}:
      t
    case False{}:
      h <> t

# A parameter name without its quantity mark (+x, -x, ~x).
def Cs.strip_sigil(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Cs.strip_sigil.go(Char.is_eq(h, '+') || Char.is_eq(h, '-') || Char.is_eq(h, '~'), h, t)

type Css is Data:
  CssNil{}
  CssCon{head: List<&2, Char>, tail: Css}

def Css.reverse(xs: Css, acc: Css) -> Css:
  match xs:
    case CssNil{}:
      acc
    case CssCon{h, t}:
      Css.reverse(t, CssCon{h, acc})

def Cs.split.cur(hit: Bool, h: Char, cur: List<&2, Char>) -> List<&2, Char>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      h <> cur

def Cs.split.acc(hit: Bool, cur: List<&2, Char>, acc: Css) -> Css:
  match hit:
    case True{}:
      CssCon{Cs.reverse(cur, Nil{}), acc}
    case False{}:
      acc

# Splits on every `sep`.
def Cs.split(cs: List<&2, Char>, +sep: Char, +cur: List<&2, Char>, acc: Css) -> Css:
  match cs:
    case Nil{}:
      Css.reverse(CssCon{Cs.reverse(cur, Nil{}), acc}, CssNil{})
    case Con{+h, t}:
      +hit = Char.is_eq(h, sep)
      Cs.split(t, sep, Cs.split.cur(hit, h, cur), Cs.split.acc(hit, cur, acc))

# ================================================================ string lists

type Strs is Data:
  StrsNil{}
  StrsCon{head: String, tail: Strs}

def Strs.has(xs: Strs, +s: String) -> Bool:
  match xs:
    case StrsNil{}:
      False{}
    case StrsCon{h, t}:
      String.eq(h, s) || Strs.has(t, s)

def Strs.len(xs: Strs) -> Nat:
  match xs:
    case StrsNil{}:
      0n
    case StrsCon{_, t}:
      1n+Strs.len(t)

def Strs.reverse(xs: Strs, acc: Strs) -> Strs:
  match xs:
    case StrsNil{}:
      acc
    case StrsCon{h, t}:
      Strs.reverse(t, StrsCon{h, acc})

def Strs.join(xs: Strs, +sep: String) -> String:
  match xs:
    case StrsNil{}:
      ""
    case StrsCon{h, StrsNil{}}:
      h
    case StrsCon{h, t}:
      h ++ sep ++ Strs.join(t, sep)

def Strs.add_new.go(known: Bool, s: String, xs: Strs) -> Strs:
  match known:
    case True{}:
      xs
    case False{}:
      StrsCon{s, xs}

def Strs.add_new(+xs: Strs, +s: String) -> Strs:
  Strs.add_new.go(Strs.has(xs, s), s, xs)

def Strs.union(xs: Strs, +ys: Strs) -> Strs:
  match xs:
    case StrsNil{}:
      ys
    case StrsCon{h, t}:
      Strs.union(t, Strs.add_new(ys, h))

def sel(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Cs.has(cs: List<&2, Char>, +c: Char) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Char.is_eq(h, c) || Cs.has(t, c)

def Cs.len(cs: List<&2, Char>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{_, t}:
      1n+Cs.len(t)

# Splits on the commas that are not inside <...>.
def Cs.split_top(cs: List<&2, Char>, +depth: U32, +cur: List<&2, Char>, acc: Css) -> Css:
  match cs:
    case Nil{}:
      Css.reverse(CssCon{Cs.reverse(cur, Nil{}), acc}, CssNil{})
    case Con{+h, t}:
      +cut = Char.is_eq(h, ',') && U32.is_zero(depth)
      Cs.split_top(t, sel(Char.is_eq(h, '<'), (depth + 1 : U32), sel(Char.is_eq(h, '>'), (depth - 1 : U32), depth)), Cs.split.cur(cut, h, cur), Cs.split.acc(cut, cur, acc))

# What is between the first '<' and the final '>' of a generic like List<&2, U32>.
def Cs.inside(cs: List<&2, Char>) -> List<&2, Char>:
  Cs.reverse(Cs.drop(Cs.reverse(Cs.after(cs, '<'), Nil{}), 1n), Nil{})

# A quantity argument (&2, or a lowercase name like `a`): TypeScript has no such thing.
def Cs.is_quantity(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Char.is_eq(h, '&') || (Char.is_lower(h) && Cs.all_word(t))

def Css.keep.go(drop: Bool, h: List<&2, Char>, rest: Css) -> Css:
  match drop:
    case True{}:
      rest
    case False{}:
      CssCon{h, rest}

# The type arguments of a generic, without the quantities.
def Css.types_only(xs: Css) -> Css:
  match xs:
    case CssNil{}:
      CssNil{}
    case CssCon{+h, t}:
      Css.keep.go(Cs.is_quantity(Cs.trim(h)), Cs.trim(h), Css.types_only(t))

# ================================================================ TypeScript types

# A TS type: its text, the opaque Bend types it mentions, the built-in generics it uses (List,
# Maybe), and the Bend types that have no TS translation (an error).
type T is Data:
  T{text: String, opaque: Strs, builtins: Strs, bad: Strs}

type Ts is Data:
  TsNil{}
  TsCon{head: T, tail: Ts}

def T.ok(s: String) -> T:
  T{s, StrsNil{}, StrsNil{}, StrsNil{}}

def T.opaque(+n: String) -> T:
  T{n, StrsCon{n, StrsNil{}}, StrsNil{}, StrsNil{}}

def T.bad(n: String) -> T:
  T{"unknown", StrsNil{}, StrsNil{}, StrsCon{n, StrsNil{}}}

def T.text(t: T) -> String:
  match t:
    case T{s, _, _, _}:
      s

# Two types side by side: "a, b", everything they mention merged.
def T.cat(a: T, b: T) -> T:
  match a b:
    case T{s1, o1, g1, x1} T{s2, o2, g2, x2}:
      T{s1 ++ ", " ++ s2, Strs.union(o1, o2), Strs.union(g1, g2), Strs.union(x1, x2)}

def T.all(ts: Ts) -> T:
  match ts:
    case TsNil{}:
      T.ok("")
    case TsCon{h, TsNil{}}:
      h
    case TsCon{h, t}:
      T.cat(h, T.all(t))

def T.apply.builtin(builtin: Bool, name: String, g: Strs) -> Strs:
  match builtin:
    case True{}:
      Strs.add_new(g, name)
    case False{}:
      g

def T.apply(+name: String, builtin: Bool, args: T) -> T:
  match args:
    case T{s, o, g, x}:
      T{name ++ "<" ++ s ++ ">", o, T.apply.builtin(builtin, name, g), x}

def ts.pick(num: Bool, str: Bool, unit: Bool, bool: Bool, known: Bool, name: Bool, +s: String) -> T:
  match num str unit bool known name:
    case True{} _ _ _ _ _:
      T.ok("number")
    case False{} True{} _ _ _ _:
      T.ok("string")
    case False{} False{} True{} _ _ _:
      T.ok("void")
    case False{} False{} False{} True{} _ _:
      T.ok("boolean")
    case False{} False{} False{} False{} True{} _:
      T.ok(s)
    case False{} False{} False{} False{} False{} True{}:
      T.opaque(s)
    case False{} False{} False{} False{} False{} False{}:
      T.bad(s)

# A type with no arguments: a primitive, a type parameter, a marked type, or else opaque.
def ts.plain(+cs: List<&2, Char>, params: Strs, unions: Strs) -> T:
  +s = String.from_list(cs)
  ts.pick(Cs.eq(cs, Cs.lit("U32")) || Cs.eq(cs, Cs.lit("Nat")) || Cs.eq(cs, Cs.lit("F32")), Cs.eq(cs, Cs.lit("String")), Cs.eq(cs, Cs.lit("Unit")), Cs.eq(cs, Cs.lit("Bool")), Strs.has(params, s) || Strs.has(unions, s), Cs.is_type_name(cs), s)

def ts.generic.go(known: Bool, builtin: Bool, name: String, cs: List<&2, Char>, args: Ts) -> T:
  match known:
    case True{}:
      T.apply(name, builtin, T.all(args))
    case False{}:
      T.bad(String.from_list(cs))

# A generic like List<&2, Step>: known when it is List, Maybe or a marked type.
def ts.generic(+name: String, cs: List<&2, Char>, unions: Strs, args: Ts) -> T:
  +builtin = String.eq(name, "List") || String.eq(name, "Maybe")
  ts.generic.go(builtin || Strs.has(unions, name), builtin, name, cs, args)

def ts.node(generic: Bool, +cs: List<&2, Char>, params: Strs, unions: Strs, args: Ts) -> T:
  match generic:
    case True{}:
      ts.generic(String.from_list(Cs.trim(Cs.before(cs, '<'))), cs, unions, args)
    case False{}:
      ts.plain(cs, params, unions)

# Translates a list of Bend type expressions. `fuel` (the text's length) bounds the nesting.
def ts.list(+fuel: Nat, xs: Css, +params: Strs, +unions: Strs) -> Ts:
  match fuel xs:
    case _ CssNil{}:
      TsNil{}
    case 0n CssCon{h, _}:
      TsCon{T.bad(String.from_list(h)), TsNil{}}
    case 1n+f CssCon{+h, rest}:
      +cs = Cs.trim(h)
      TsCon{ts.node(Cs.has(cs, '<'), cs, params, unions, ts.list(f, Css.types_only(Cs.split_top(Cs.inside(cs), 0, Nil{}, CssNil{})), params, unions)), ts.list(f, rest, params, unions)}

def Ts.first(ts: Ts) -> T:
  match ts:
    case TsCon{h, _}:
      h
    case TsNil{}:
      T.bad("")

# The TypeScript type of a Bend type expression, given the type parameters in scope and the marked types.
def ts_expr(+cs: List<&2, Char>, params: Strs, unions: Strs) -> T:
  Ts.first(ts.list(1n+Cs.len(cs), CssCon{cs, CssNil{}}, params, unions))

# The same, for a type written as text, with nothing in scope.
def ts_type(t: String) -> T:
  ts_expr(String.to_list(t), StrsNil{}, StrsNil{})

# ================================================================ reading the file

# What the generator has seen: TS function lines, union texts, the merged mentions, the pending
# doc comment, whether a "# ts: union" mark is pending, the marked types, and the union being read.
type U is Data:
  UNone{}
  UIn{name: String, params: Strs, variants: Strs}

type Acc is Data:
  Acc{fns: Strs, unions_out: Strs, seen: T, doc: Strs, mark: Bool, unions: Strs, cur: U}

def Acc.empty(unions: Strs) -> Acc:
  Acc{StrsNil{}, StrsNil{}, T.ok(""), StrsNil{}, False{}, unions, UNone{}}

def T.mention(seen: T, t: T) -> T:
  match seen t:
    case T{s, o1, g1, x1} T{_, o2, g2, x2}:
      T{s, Strs.union(o2, o1), Strs.union(g2, g1), Strs.union(x2, x1)}

def doc.text.go(empty: Bool, doc: Strs) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      "  /** " ++ Strs.join(Strs.reverse(doc, StrsNil{}), " ") ++ " */\n"

def doc.text(+doc: Strs) -> String:
  doc.text.go(U32.is_zero(U32.from_nat(Strs.len(doc))), doc)

def name.of(p: List<&2, Char>) -> String:
  String.from_list(Cs.trim(Cs.strip_sigil(Cs.trim(Cs.before(p, ':')))))

# Joins named parts with ", " (an empty rest adds nothing).
def params.ts.cat(a: T, b: T) -> T:
  match a b:
    case T{s1, o1, g1, x1} T{"", o2, g2, x2}:
      T{s1, Strs.union(o1, o2), Strs.union(g1, g2), Strs.union(x1, x2)}
    case _ _:
      T.cat(a, b)

def T.with_name(n: String, sep: String, t: T) -> T:
  match t:
    case T{s, o, g, x}:
      T{n ++ sep ++ s, o, g, x}

# "+g: Game, n: U32" as TS "g: Game, n: number", and the types mentioned.
def params.ts(ps: Css, +params: Strs, +unions: Strs, +sep: String) -> T:
  match ps:
    case CssNil{}:
      T.ok("")
    case CssCon{+p, rest}:
      params.ts.cat(T.with_name(name.of(p), sep, ts_expr(Cs.trim(Cs.after(p, ':')), params, unions)), params.ts(rest, params, unions, sep))

def params.split.go(empty: Bool, cs: List<&2, Char>) -> Css:
  match empty:
    case True{}:
      CssNil{}
    case False{}:
      Cs.split_top(cs, 0, Nil{}, CssNil{})

def params.split(+cs: List<&2, Char>) -> Css:
  params.split.go(Cs.eq(Cs.trim(cs), Nil{}), cs)

# One `def api_name(params) -> Ret:` line as a TS function line.
def Acc.def(a: Acc, +line: List<&2, Char>) -> Acc:
  match a:
    case Acc{fns, us, seen, +doc, mark, +unions, cur}:
      +rest = Cs.drop(line, 4n)
      +inner = Cs.after(rest, '(')
      +ps = params.ts(params.split(Cs.before(inner, ')')), StrsNil{}, unions, ": ")
      +ret = ts_expr(Cs.trim(Cs.before(Cs.after(Cs.after(inner, ')'), '>'), ':')), StrsNil{}, unions)
      Acc{StrsCon{doc.text(doc) ++ "  " ++ String.from_list(Cs.before(rest, '(')) ++ "(" ++ T.text(ps) ++ "): " ++ T.text(ret) ++ ";", fns}, us, T.mention(T.mention(seen, ps), ret), StrsNil{}, False{}, unions, cur}

def type.params.go(keep: Bool, n: String, rest: Strs) -> Strs:
  match keep:
    case True{}:
      StrsCon{n, rest}
    case False{}:
      rest

# The type parameters of a header like `type Maybe<a, -A: Kind(a)> is Kind(a):` (only the -A ones).
def type.params(xs: Css) -> Strs:
  match xs:
    case CssNil{}:
      StrsNil{}
    case CssCon{+p, rest}:
      type.params.go(Cs.starts(Cs.trim(p), Cs.lit("-")), name.of(p), type.params(rest))

def type.name(line: List<&2, Char>) -> String:
  String.from_list(Cs.trim(Cs.before(Cs.before(Cs.drop(line, 5n), '<'), ' ')))

def Acc.start_union(a: Acc, +line: List<&2, Char>) -> Acc:
  match a:
    case Acc{f, us, s, _, _, un, _}:
      Acc{f, us, s, StrsNil{}, False{}, un, UIn{type.name(line), type.params(Cs.split_top(Cs.before(Cs.after(line, '<'), '>'), 0, Nil{}, CssNil{})), StrsNil{}}}

def Strs.to_list(xs: Strs) -> List<&2, String>:
  match xs:
    case StrsNil{}:
      Nil{}
    case StrsCon{h, t}:
      h <> Strs.to_list(t)

def Css.to_strs(xs: Css) -> Strs:
  match xs:
    case CssNil{}:
      StrsNil{}
    case CssCon{h, t}:
      StrsCon{String.from_list(Cs.trim(h)), Css.to_strs(t)}

def Strs.split_fields(s: String) -> Strs:
  Css.to_strs(Cs.split_top(String.to_list(s), 0, Nil{}, CssNil{}))

def variant.fields.go(empty: Bool, s: String) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      "; " ++ String.join(Strs.to_list(Strs.split_fields(s)), "; ")

def variant.fields(+s: String) -> String:
  variant.fields.go(String.eq(s, ""), s)

# A constructor line `  Winner{side: Side}` as the TS variant `| { $: "Winner"; side: Side }`.
def Acc.variant(a: Acc, +line: List<&2, Char>) -> Acc:
  match a:
    case Acc{f, us, s, d, m, +un, UIn{n, +ps, vs}}:
      +cs = Cs.trim(line)
      +fields = params.ts(params.split(Cs.before(Cs.after(cs, '{'), '}')), ps, un, ": ")
      Acc{f, us, T.mention(s, fields), d, m, un, UIn{n, ps, StrsCon{"  | { $: \"" ++ String.from_list(Cs.before(cs, '{')) ++ "\"" ++ variant.fields(T.text(fields)) ++ " }", vs}}}
    case _:
      a

def params.text.go(empty: Bool, ps: Strs) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      "<" ++ Strs.join(ps, ", ") ++ ">"

def union.text(n: String, +ps: Strs, vs: Strs) -> String:
  "export type " ++ n ++ params.text.go(U32.is_zero(U32.from_nat(Strs.len(ps))), ps) ++ " =\n" ++ Strs.join(Strs.reverse(vs, StrsNil{}), "\n") ++ ";\n"

# Ends the union being read, if any.
def Acc.close(a: Acc) -> Acc:
  match a:
    case Acc{f, us, s, d, m, un, UIn{n, ps, vs}}:
      Acc{f, StrsCon{union.text(n, ps, vs), us}, s, d, m, un, UNone{}}
    case _:
      a

def Acc.comment(a: Acc, line: List<&2, Char>) -> Acc:
  match a:
    case Acc{f, us, s, d, m, un, c}:
      Acc{f, us, s, StrsCon{String.from_list(Cs.drop(line, 2n)), d}, m, un, c}

def Acc.marked(a: Acc) -> Acc:
  match a:
    case Acc{f, us, s, d, _, un, c}:
      Acc{f, us, s, d, True{}, un, c}

def Acc.other(a: Acc) -> Acc:
  match a:
    case Acc{f, us, s, _, _, un, c}:
      Acc{f, us, s, StrsNil{}, False{}, un, c}

def Acc.mark(a: Acc) -> Bool:
  match a:
    case Acc{_, _, _, _, m, _, _}:
      m

def Acc.in_union(a: Acc) -> Bool:
  match a:
    case Acc{_, _, _, _, _, _, UIn{_, _, _}}:
      True{}
    case _:
      False{}

def Acc.normal.go(api: Bool, mark: Bool, start: Bool, doc: Bool, a: Acc, line: List<&2, Char>) -> Acc:
  match api mark start doc:
    case True{} _ _ _:
      Acc.def(a, line)
    case False{} True{} _ _:
      Acc.marked(a)
    case False{} False{} True{} _:
      Acc.start_union(a, line)
    case False{} False{} False{} True{}:
      Acc.comment(a, line)
    case False{} False{} False{} False{}:
      Acc.other(a)

def Acc.normal(+a: Acc, +line: List<&2, Char>) -> Acc:
  Acc.normal.go(Cs.starts(line, Cs.lit("def api_")), Cs.eq(Cs.trim(line), Cs.lit("# ts: union")), Acc.mark(a) && Cs.starts(line, Cs.lit("type ")), Cs.starts(line, Cs.lit("# ")) && Bool.not(Cs.starts(line, Cs.lit("# ="))), a, line)

def Acc.line.go(variant: Bool, a: Acc, line: List<&2, Char>) -> Acc:
  match variant:
    case True{}:
      Acc.variant(a, line)
    case False{}:
      Acc.normal(Acc.close(a), line)

def Acc.line(+a: Acc, +line: List<&2, Char>) -> Acc:
  Acc.line.go(Acc.in_union(a) && Cs.starts(line, Cs.lit("  ")) && Cs.has(line, '{'), a, line)

def Acc.lines(ls: Css, a: Acc) -> Acc:
  match ls:
    case CssNil{}:
      a
    case CssCon{l, rest}:
      Acc.lines(rest, Acc.line(a, l))

# First pass: the names of the types marked with "# ts: union".
def marked.add(take: Bool, line: List<&2, Char>, acc: Strs) -> Strs:
  match take:
    case True{}:
      StrsCon{type.name(line), acc}
    case False{}:
      acc

def marked(ls: Css, pending: Bool, acc: Strs) -> Strs:
  match ls:
    case CssNil{}:
      acc
    case CssCon{+l, rest}:
      marked(rest, Cs.eq(Cs.trim(l), Cs.lit("# ts: union")), marked.add(pending && Cs.starts(l, Cs.lit("type ")), l, acc))

def builtin.text.go(list: Bool, n: String) -> String:
  match list:
    case True{}:
      "export type List<A> =\n  | { $: \"Nil\" }\n  | { $: \"Con\"; head: A; tail: List<A> };\n"
    case False{}:
      "export type Maybe<A> =\n  | { $: \"None\" }\n  | { $: \"Some\"; value: A };\n"

# ================================================================ output

def builtin.text(+n: String) -> String:
  builtin.text.go(String.eq(n, "List"), n)

def builtins.text(xs: Strs) -> String:
  match xs:
    case StrsNil{}:
      ""
    case StrsCon{h, t}:
      builtin.text(h) ++ builtins.text(t)

def types.text(xs: Strs) -> String:
  match xs:
    case StrsNil{}:
      ""
    case StrsCon{+h, t}:
      "export type " ++ h ++ " = Bend<\"" ++ h ++ "\">;\n" ++ types.text(t)

def errs.text(xs: Strs) -> Strs:
  match xs:
    case StrsNil{}:
      StrsNil{}
    case StrsCon{h, t}:
      StrsCon{"no TS mapping for Bend type \"" ++ h ++ "\"", errs.text(t)}

# The result: the declaration text, how many functions, and the errors (none when it worked).
type Out is Data:
  Out{text: String, count: Nat, errs: Strs}

def decls.text(src: String, o: Strs, g: Strs, us: Strs) -> String:
  "// Generated from " ++ src ++ " by tools/dts. Do not edit: run it again after changing the engine.\n" ++
    "declare const bend: unique symbol;\n" ++
    "/** A value owned by the Bend engine: keep it and pass it back, never look inside. */\n" ++
    "export type Bend<Name extends string> = { readonly [bend]: Name };\n" ++
    types.text(Strs.reverse(o, StrsNil{})) ++ builtins.text(Strs.reverse(g, StrsNil{})) ++ Strs.join(Strs.reverse(us, StrsNil{}), "")

# Declarations next to the compiled .mjs (a .d.mts file).
def Out.make(src: String, a: Acc) -> Out:
  match a:
    case Acc{+fns, us, T{_, o, g, x}, _, _, _, _}:
      Out{decls.text(src, o, g, us) ++ "\ndeclare const engine: {\n" ++ Strs.join(Strs.reverse(fns, StrsNil{}), "\n") ++ "\n};\nexport default engine;\n", Strs.len(fns), errs.text(Strs.reverse(x, StrsNil{}))}

def Cs.append(xs: List<&2, Char>, ys: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> Cs.append(t, ys)

def Cs.replace.pick(hit: Bool, a: List<&2, Char>, b: List<&2, Char>) -> List<&2, Char>:
  match hit:
    case True{}:
      a
    case False{}:
      b

# The text with the first `pat` replaced by `rep`.
def Cs.replace_first(cs: List<&2, Char>, +pat: List<&2, Char>, +rep: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Cs.replace.pick(Cs.starts(h <> t, pat), Cs.append(rep, Cs.drop(h <> t, Cs.len(pat))), h <> Cs.replace_first(t, pat, rep))

# One TypeScript module: the declarations, an Engine interface, and the compiled code typed as it.
def Out.make_ts(src: String, a: Acc, js: String) -> Out:
  match a:
    case Acc{+fns, us, T{_, o, g, x}, _, _, _, _}:
      Out{"// @ts-nocheck: the code below is compiled from Bend; importers still get the types.\n" ++ decls.text(src, o, g, us) ++
        "\nexport interface Engine {\n" ++ Strs.join(Strs.reverse(fns, StrsNil{}), "\n") ++ "\n}\n\n" ++
        String.from_list(Cs.replace_first(String.to_list(js), Cs.lit("export default {"), Cs.lit("const engine = {"))) ++
        "\nexport default engine as unknown as Engine;\n", Strs.len(fns), errs.text(Strs.reverse(x, StrsNil{}))}

def lines.of(text: String) -> Css:
  Cs.split(String.to_list(text), '\n', Nil{}, CssNil{})

def read.all(+text: String) -> Acc:
  Acc.close(Acc.lines(lines.of(text), Acc.empty(marked(lines.of(text), False{}, StrsNil{}))))

# The declarations for the Bend source `text` (read from the file named `src`).
def dts(src: String, text: String) -> Out:
  Out.make(src, read.all(text))

# The TypeScript module for the Bend source `text` and its compiled JavaScript `js`.
def ts_module(src: String, text: String, js: String) -> Out:
  Out.make_ts(src, read.all(text), js)

# ================================================================ single pieces (used by the laws)

# A line that declares part of the public API.
def is_api(line: String) -> Bool:
  Cs.starts(String.to_list(line), Cs.lit("def api_"))

def line_fn.some(a: Acc) -> Maybe<String>:
  match a:
    case Acc{StrsCon{f, _}, _, _, _, _, _, _}:
      Some{f}
    case _:
      None{}

def line_fn.go(api: Bool, line: String) -> Maybe<String>:
  match api:
    case True{}:
      line_fn.some(Acc.def(Acc.empty(StrsNil{}), String.to_list(line)))
    case False{}:
      None{}

# The TS function line a single source line yields, if it is part of the API.
def line_fn(+line: String) -> Maybe<String>:
  line_fn.go(is_api(line), line)

def Out.text(o: Out) -> String:
  match o:
    case Out{t, _, _}:
      t

# The first union a source yields (used by the laws).
def union_of.pick(a: Acc) -> String:
  match a:
    case Acc{_, StrsCon{u, _}, _, _, _, _, _}:
      u
    case _:
      ""

def union_of(src: String) -> String:
  union_of.pick(read.all(src))
