# proofs of laws/ErrTextShowsUsage.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/ErrTextShowsUsage.bend as Laws
import ../laws/defs/HelpPages.bend as D1

# the usage walk reads the usage line of the page it reaches
def hl.usage(
  path: List<&2, String>,
  how: S.How
) -> {S.usage.go(path, how) == D1.usage_line(D1.reach(path, how)) : String}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, _g, _s, _u}:
          {==}
    case Con{+hh, tt}:
      hl.usage(tt, S.help.step(how, hh))

def Laws.err_path_at(_at, _word, _name, _value):
  {==}

# the usage line an error's text shows is the one its command's page shows
def et.usage(
  spec: Shake.Cli,
  +path: List<&2, String>
) -> {S.usage.at(spec, path) == D1.usage_line(D1.reach(path, D1.root(spec))) : String}:
  match spec:
    case S.Cli{+name, +about, +version, +args, +subs}:
      hl.usage(path, S.How{name, about, version, args, subs, name})

# an error's text, with its usage line read as its page's
def et.wrap(
  +spec: Shake.Cli,
  +at: List<&2, String>,
  +msg: String
) -> {S.err.wrap(spec, at, msg)
    == msg ++ "\n\n" ++ D1.usage_line(D1.reach(at, D1.root(spec))) ++ "\n\n" ++ S.err.hint(at) : String}:
  Equal.cong(String, String, uu => msg ++ "\n\n" ++ uu ++ "\n\n" ++ S.err.hint(at), S.usage.at(spec, at),
    D1.usage_line(D1.reach(at, D1.root(spec))), et.usage(spec, at))

# what `err_text_usage` claims of an error
def et.ty(+spec: Shake.Cli, +err: Shake.ParseErr) -> Type:
  &msg: String -> {Shake.err_text(spec, err)
    == msg ++ "\n\n" ++ D1.usage_line(D1.reach(Shake.err_path(err), D1.root(spec))) ++ "\n\n" ++
      S.err.hint(Shake.err_path(err)) : String}

# Unit for None, Empty for Some: a motive that tells them apart
def et.none_ty(mm: Maybe<&2, List<&2, String>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_p}:
      Empty

# a request for help has a help path
def et.some_none(+path: List<&2, String>, hh: {Some{path} == None{} : Maybe<&2, List<&2, String>>}) -> Empty:
  ee = Equal.sym(Maybe<&2, List<&2, String>>, Some{path}, None{}, hh)
  %ee : et.none_ty(_)
  Unit{}

def Laws.err_text_usage(spec, err, h_err, h_ver):
  match err:
    case S.UnknownFlag{+at, +word}:
      ("error: unexpected argument '" ++ word ++ "' found" ++ S.sug.tip(S.sug.word(spec, at, word)),
        et.wrap(spec, at, "error: unexpected argument '" ++ word ++ "' found" ++ S.sug.tip(S.sug.word(spec, at, word))))
    case S.Missing{+at, +name}:
      ("error: the following required argument was not provided:\n  " ++ S.err.name(spec, at, name),
        et.wrap(spec, at, "error: the following required argument was not provided:\n  " ++ S.err.name(spec, at, name)))
    case S.NoValue{+at, +name}:
      ("error: a value is required for '" ++ S.err.name(spec, at, name) ++ "' but none was supplied",
        et.wrap(spec, at, "error: a value is required for '" ++ S.err.name(spec, at,
            name) ++ "' but none was supplied"))
    case S.BadValue{+at, +name, +value}:
      ("error: invalid value '" ++ value ++ "' for '" ++ S.err.name(spec, at, name) ++ "'" ++
          S.err.values(S.err.find(spec, at, name)),
        et.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ S.err.name(spec, at, name) ++ "'" ++
          S.err.values(S.err.find(spec, at, name))))
    case S.NeedHelp{+path}:
      Empty.absurd(et.ty(spec, S.NeedHelp{path}), et.some_none(path, h_err))
    case S.NeedVersion{}:
      Empty.absurd(et.ty(spec, S.NeedVersion{}), Walk.wk.true_false(h_ver))
    case S.Unexpected{+at, +arg}:
      ("error: unexpected argument '" ++ arg ++ "' found",
        et.wrap(spec, at, "error: unexpected argument '" ++ arg ++ "' found"))
    case S.Repeated{+at, +name}:
      ("error: the argument '" ++ S.err.name(spec, at, name) ++ "' cannot be used multiple times",
        et.wrap(spec, at, "error: the argument '" ++ S.err.name(spec, at, name) ++ "' cannot be used multiple times"))
