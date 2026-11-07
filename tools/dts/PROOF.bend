import Base
import ./dts.bend as D
import ./LAWS.bend as Laws

# The mappings and the examples are checked by running them inside the checker.
def Laws.u32_is_number():
  {==}

def Laws.nat_is_number():
  {==}

def Laws.string_is_string():
  {==}

def Laws.engine_types_are_opaque():
  {==}

def Laws.known_generics_stay_generic():
  {==}

def Laws.unknown_generics_are_refused():
  {==}

def Laws.marked_type_becomes_union():
  {==}

def Laws.type_parameters_stay_generic():
  {==}

def Laws.example_line():
  {==}

# For any line: line_fn branches on is_api, and the premise says which branch it takes.
def Laws.only_api_lines_count(line, not_api):
  %Equal.sym(Bool, D.is_api(line), False{}, not_api) : {D.line_fn.go(_, line) == None{} : Maybe<String>}
  {==}
