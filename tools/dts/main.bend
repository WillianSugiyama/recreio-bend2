import Base
import ./dts.bend as D

# usage: bend-dts game.bend web/game.d.mts            (types next to the compiled .mjs)
#        bend-dts game.bend web/game.ts web/game.mjs  (one TypeScript module: types + code)
# (or build it once: bend tools/dts/main.bend -o tools/dts/bend-dts, then tools/dts/bend-dts game.bend web/game.d.mts)

def read.text(r: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case (f, rt):
      do IO<String>:
        text : String <- IO.try(String, IO.pure(Result<&1, &1, U32 & String, String>, rt))
        File.close(f)
        return text

def read.size(r: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  match r:
    case (f, rs):
      do IO<String>:
        size : U32 <- IO.try(U32, IO.pure(Result<&1, &1, U32 & String, U32>, rs))
        r2 : File & Result<&1, &1, U32 & String, String> <- File.read(f, size)
        read.text(r2)

def read_all(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read.size(r)

def write.done(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match r:
    case (f, rw):
      do IO<Unit>:
        done : Unit <- IO.try(Unit, IO.pure(Result<&1, &1, U32 & String, Unit>, rw))
        File.close(f)

def write_all(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
    write.done(r)

def finish(out: D.Out, +dest: String) -> IO(Unit):
  match out:
    case D.Out{text, n, D.StrsNil{}}:
      do IO<Unit>:
        write_all(dest, text)
        IO.print("bend-dts: " ++ U32.show(U32.from_nat(n)) ++ " functions -> " ++ dest)
    case D.Out{_, _, errs}:
      IO.die(Unit, 1, "bend-dts: " ++ D.Strs.join(errs, "; "))

def run(args: List<String>) -> IO(Unit):
  match args:
    case Con{_, Con{+src, Con{dest, Nil{}}}}:
      do IO<Unit>:
        text : String <- read_all(src)
        finish(D.dts(src, text), dest)
    case Con{_, Con{+src, Con{dest, Con{js, Nil{}}}}}:
      do IO<Unit>:
        text : String <- read_all(src)
        code : String <- read_all(js)
        finish(D.ts_module(src, text, code), dest)
    case _:
      IO.die(Unit, 2, "usage: bend-dts <file.bend> <out.d.mts>   or   bend-dts <file.bend> <out.ts> <compiled.mjs>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args)
