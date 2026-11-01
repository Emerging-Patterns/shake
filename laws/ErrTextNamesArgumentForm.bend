# `err_text` names the argument of a `Missing{at, name}`, `NoValue{at, name}`,
# `BadValue{at, name, value}` or `Repeated{at, name}` error by the **display
# form** of the argument named `name` of the deepest command on the path `at`
# that has one, the root first and each name of `at` reached as `help` reaches
# it (laws/HelpFollowsPath.bend): for a flag, `--` and its long spelling, else `-` and its
# short spelling; for an option, the same followed by ` <NAME>`, and by `...`
# for one built with `many`; for a positional, `<NAME>` when it is required
# and `[NAME]` otherwise, followed by `...` for a rest; `NAME` being the
# argument's name in upper case. A flag or option with neither spelling (an
# empty spelling counts as none), and a name no command on the path has, is
# named by `name` itself. The message of a `BadValue` whose argument has
# nonempty choices `c1`, ..., `cn` ends with the line ` [possible values: c1,
# ..., cn]`.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1
import ./defs/HelpPages.bend as D2

# the pages a path walks through from `how`, `how` first, each name moving as
# `help` moves
def pages(path: List<&2, String>, +how: S.How) -> List<&2, S.How>:
  match path:
    case Nil{}:
      [how]
    case Con{+hh, tt}:
      how <> pages(tt, S.help.step(how, hh))

# a later find when there is one, else an earlier
def keep_later(here: Maybe<&2, S.Arg>, later: Maybe<&2, S.Arg>) -> Maybe<&2, S.Arg>:
  match later:
    case None{}:
      here
    case Some{aa}:
      Some{aa}

# the argument named `name` of the last page that has one
def deepest(hs: List<&2, S.How>, +name: String) -> Maybe<&2, S.Arg>:
  match hs:
    case Nil{}:
      None{}
    case Con{hh, tt}:
      keep_later(S.by_name(S.help.how_args(hh), name), deepest(tt, name))

# clap's line of the values a found argument allows, when it has choices
def values_line(found: Maybe<&2, S.Arg>) -> String:
  match found:
    case None{}:
      ""
    case Some{aa}:
      S.Arg{_n, _s, _l, _k, _h, _r, _d, cs} = aa
      match cs:
        case Nil{}:
          ""
        case Con{cc, rest}:
          "\n  [possible values: " ++ String.join(cc <> rest, ", ") ++ "]"

# LAW: the argument an error is about is the one named so on the deepest
# command of its path that has one, the root first
law err_find:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +name: String
  {S.err.find(spec, at, name) == deepest(pages(at, D2.root(spec)), name) : Maybe<&2, S.Arg>}

# LAW: an argument's display form: a flag by `--long`, else `-s`, an option
# with its value mark after, a positional by `<NAME>` or `[NAME]`, `...`
# after a rest
law err_form:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +fb: S.Fallback
  for +cs: List<&2, String>
  {S.err.form(S.Arg{nn, sh, lo, kind, hp, req, fb, cs}) == D1.form_of(S.Arg{nn, sh, lo, kind, hp, req, fb,
      cs}) : String}

# LAW: a missing argument is named by its display form
law err_missing_named:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +name: String
  {Shake.err_text(spec, S.Missing{at, name})
    == S.err.wrap(spec, at, "error: the following required argument was not provided:\n  " ++
      D1.named(deepest(pages(at, D2.root(spec)), name), name)) : String}

# LAW: an option missing its value is named by its display form
law err_novalue_named:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +name: String
  {Shake.err_text(spec, S.NoValue{at, name})
    == S.err.wrap(spec, at, "error: a value is required for '" ++ D1.named(deepest(pages(at, D2.root(spec)), name),
        name) ++
      "' but none was supplied") : String}

# LAW: a value outside the choices names its argument by its display form,
# then lists the choices
law err_bad_named:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +name: String
  for +value: String
  {Shake.err_text(spec, S.BadValue{at, name, value})
    == S.err.wrap(spec, at, "error: invalid value '" ++ value ++ "' for '" ++
      D1.named(deepest(pages(at, D2.root(spec)), name), name) ++ "'" ++ values_line(deepest(pages(at, D2.root(spec)),
          name)))
    : String}

# LAW: an argument given twice is named by its display form
law err_repeated_named:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +name: String
  {Shake.err_text(spec, S.Repeated{at, name})
    == S.err.wrap(spec, at, "error: the argument '" ++ D1.named(deepest(pages(at, D2.root(spec)), name), name) ++
      "' cannot be used multiple times") : String}
