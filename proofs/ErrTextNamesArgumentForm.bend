# proofs of laws/ErrTextNamesArgumentForm.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../laws/ErrTextNamesArgumentForm.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1
import ../laws/defs/HelpPages.bend as D2
import ./lemmas/StringAppendEmpty.bend as M1

# the find kept here is the later of the one above and this one
def ef.here(
  found: Maybe<&2, S.Arg>,
  +best: Maybe<&2, S.Arg>
) -> {S.err.find.here(found, best) == Laws.keep_later(best, found) : Maybe<&2, S.Arg>}:
  match found:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# keeping the later find is associative
def ef.assoc(
  +found: Maybe<&2, S.Arg>,
  +best: Maybe<&2, S.Arg>,
  later: Maybe<&2, S.Arg>
) -> {Laws.keep_later(S.err.find.here(found, best), later)
    == Laws.keep_later(best, Laws.keep_later(found, later)) : Maybe<&2, S.Arg>}:
  match later:
    case None{}:
      ef.here(found, best)
    case Some{_a}:
      {==}

# the search down a path keeps the deepest page's find, else `best`
def ef.go(
  path: List<&2, String>,
  how: S.How,
  +name: String,
  +best: Maybe<&2, S.Arg>
) -> {S.err.find.go(path, how, name, best) == Laws.keep_later(best, Laws.deepest(Laws.pages(path, how), name))
    : Maybe<&2, S.Arg>}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, +args, _s, _u}:
          ef.here(S.by_name(args, name), best)
    case Con{+hh, +tt}:
      match how:
        case S.How{+bin, +about, +version, +args, +subs, +usage}:
          +hw = {S.How{bin, about, version, args, subs, usage} : S.How}
          +here = S.err.find.here(S.by_name(args, name), best)
          +deeper = Laws.deepest(Laws.pages(tt, S.help.step(hw, hh)), name)
          Equal.trans(Maybe<&2, S.Arg>, S.err.find.go(tt, S.help.step(hw, hh), name, here),
            Laws.keep_later(here, deeper), Laws.keep_later(best, Laws.keep_later(S.by_name(args, name), deeper)),
            ef.go(tt, S.help.step(hw, hh), name, here),
            ef.assoc(S.by_name(args, name), best, deeper))

# keeping the later of nothing and a find is the find
def ef.none(found: Maybe<&2, S.Arg>) -> {Laws.keep_later(None{}, found) == found : Maybe<&2, S.Arg>}:
  match found:
    case None{}:
      {==}
    case Some{_a}:
      {==}

def Laws.err_find(spec, at, name):
  match spec:
    case S.Cli{+bin, +about, +version, +args, +subs}:
      +hw = {S.How{bin, about, version, args, subs, bin} : S.How}
      Equal.trans(Maybe<&2, S.Arg>, S.err.find.go(at, hw, name, None{}),
        Laws.keep_later(None{}, Laws.deepest(Laws.pages(at, hw), name)), Laws.deepest(Laws.pages(at, hw), name),
        ef.go(at, hw, name, None{}), ef.none(Laws.deepest(Laws.pages(at, hw), name)))

# a string with nothing after it, under a char
def ef.nil_under(+cc: Char, xs: String) -> {SCon{cc, xs ++ ""} == SCon{cc, xs} : String}:
  Equal.cong(String, String, ys => SCon{cc, ys}, xs ++ "", xs, M1.hs.nil(xs))

def Laws.err_form(nn, _sh, _lo, kind, _hp, req, _fb, _cs):
  match kind:
    case S.Flag{}:
      {==}
    case S.Opt{}:
      {==}
    case S.Many{}:
      {==}
    case S.Pos{}:
      match req:
        case True{}:
          ef.nil_under('<', String.to_upper(nn) ++ ">")
        case False{}:
          ef.nil_under('[', String.to_upper(nn) ++ "]")
    case S.Rest{}:
      match req:
        case True{}:
          {==}
        case False{}:
          {==}

# a found argument is named as the law names it
def en.named(found: Maybe<&2, S.Arg>, +name: String) -> {S.err.named(found, name) == D1.named(found, name) : String}:
  match found:
    case None{}:
      {==}
    case Some{aa}:
      match aa:
        case S.Arg{+nn, +sh, +lo, +kind, +hp, +req, +fb, +cs}:
          Laws.err_form(nn, sh, lo, kind, hp, req, fb, cs)

# an error's argument, named as the law names it
def en.name(
  +spec: Shake.Cli,
  +at: List<&2, String>,
  +name: String
) -> {S.err.name(spec, at, name) == D1.named(Laws.deepest(Laws.pages(at, D2.root(spec)), name), name) : String}:
  +dd = Laws.deepest(Laws.pages(at, D2.root(spec)), name)
  Equal.trans(String, S.err.named(S.err.find(spec, at, name), name), S.err.named(dd, name), D1.named(dd, name),
    Equal.cong(Maybe<&2, S.Arg>, String, ff => S.err.named(ff, name), S.err.find(spec, at, name), dd,
      Laws.err_find(spec, at, name)),
    en.named(dd, name))

# a found argument's choices line is the law's
def en.values(found: Maybe<&2, S.Arg>) -> {S.err.values(found) == Laws.values_line(found) : String}:
  match found:
    case None{}:
      {==}
    case Some{aa}:
      match aa:
        case S.Arg{_n, _s, _l, _k, _h, _r, _d, cs}:
          match cs:
            case Nil{}:
              {==}
            case Con{_c, _t}:
              {==}

def Laws.err_missing_named(spec, at, name):
  Equal.cong(String, String, xx => S.err.wrap(spec, at,
      "error: the following required argument was not provided:\n  " ++ xx),
    S.err.name(spec, at, name), D1.named(Laws.deepest(Laws.pages(at, D2.root(spec)), name), name),
    en.name(spec, at, name))

def Laws.err_novalue_named(spec, at, name):
  Equal.cong(String, String, xx => S.err.wrap(spec, at,
      "error: a value is required for '" ++ xx ++ "' but none was supplied"),
    S.err.name(spec, at, name), D1.named(Laws.deepest(Laws.pages(at, D2.root(spec)), name), name),
    en.name(spec, at, name))

def Laws.err_repeated_named(spec, at, name):
  Equal.cong(String, String, xx => S.err.wrap(spec, at,
      "error: the argument '" ++ xx ++ "' cannot be used multiple times"),
    S.err.name(spec, at, name), D1.named(Laws.deepest(Laws.pages(at, D2.root(spec)), name), name),
    en.name(spec, at, name))

def Laws.err_bad_named(spec, at, name, value):
  +dd = Laws.deepest(Laws.pages(at, D2.root(spec)), name)
  +ff = S.err.find(spec, at, name)
  Equal.trans(String,
    S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ S.err.named(ff,
        name) ++ "'" ++ S.err.values(ff)),
    S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ S.err.named(dd,
        name) ++ "'" ++ S.err.values(dd)),
    S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ D1.named(dd,
        name) ++ "'" ++ Laws.values_line(dd)),
    Equal.cong(Maybe<&2, S.Arg>, String,
      gg => S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ S.err.named(gg, name) ++ "'" ++
        S.err.values(gg)), ff, dd, Laws.err_find(spec, at, name)),
    Equal.trans(String,
      S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ S.err.named(dd,
          name) ++ "'" ++ S.err.values(dd)),
      S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ D1.named(dd,
          name) ++ "'" ++ S.err.values(dd)),
      S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++ D1.named(dd,
          name) ++ "'" ++ Laws.values_line(dd)),
      Equal.cong(String, String, xx => S.err.wrap(spec, at,
          "error: invalid value '" ++ value ++ "' for '" ++ xx ++ "'" ++
        S.err.values(dd)), S.err.named(dd, name), D1.named(dd, name), en.named(dd, name)),
      Equal.cong(String, String, xx => S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++
        D1.named(dd, name) ++ "'" ++ xx), S.err.values(dd), Laws.values_line(dd), en.values(dd))))
