import Base
import ./dts.bend as D

# Leis do gerador de tipos TypeScript (tools/dts).

# Numeros do Bend viram number no TS.
law u32_is_number:
  {D.T.text(D.ts_type("U32")) == "number" : String}

law nat_is_number:
  {D.T.text(D.ts_type("Nat")) == "number" : String}

# Texto vira string.
law string_is_string:
  {D.T.text(D.ts_type("String")) == "string" : String}

# Tipo da engine sem marca vira tipo opaco: o TS guarda, mas nao enxerga dentro.
law engine_types_are_opaque:
  {D.ts_type("Game") == D.T.opaque("Game") : D.T}

# Generics conhecidos (List, Maybe e tipos marcados) viram generics do TS; as quantidades (&2) somem.
law known_generics_stay_generic:
  {D.T.text(D.ts_type("List<&2, Maybe<U32>>")) == "List<Maybe<number>>" : String}

# Generics desconhecidos (Sigma, tipos que dependem de valores...) sao recusados em vez de virar tipo errado.
law unknown_generics_are_refused:
  {D.ts_type("Sigma<&1, &1, U32, U32>") == D.T.bad("Sigma<&1, &1, U32, U32>") : D.T}

# Um tipo marcado com "# ts: union" vira uma uniao com uma variante por construtor.
law marked_type_becomes_union:
  {D.union_of("# ts: union\ntype Outcome is Data:\n  Ongoing{}\n  Winner{side: U32}\n  Draw{}\n") == "export type Outcome =\n  | { $: \"Ongoing\" }\n  | { $: \"Winner\"; side: number }\n  | { $: \"Draw\" };\n" : String}

# O parametro de tipo de um tipo marcado vira parametro generico no TS.
law type_parameters_stay_generic:
  {D.union_of("# ts: union\ntype Box<a, -A: Kind(a)> is Kind(a):\n  Box{value: A}\n") == "export type Box<A> =\n  | { $: \"Box\"; value: A };\n" : String}

# Linha que nao declara API nao gera nada no TS.
law only_api_lines_count:
  for +line: String
  for not_api: {D.is_api(line) == False{} : Bool}
  {D.line_fn(line) == None{} : Maybe<String>}

# Um exemplo completo: a assinatura em Bend e a linha TS que sai dela.
law example_line:
  {D.line_fn("def api_play(+g: Game, code: U32) -> Game:") == Some{"  api_play(g: Game, code: number): Game;"} : Maybe<String>}
