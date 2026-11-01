# the names, spellings and reports of a command's arguments
import Base
import ../../src/cli.bend as S
import ../../src/check.bend as K

# whether an option of this kind binds a value given it now: one built with
# `opt` when it was not given before, one built with `many` always
def takes(kk: S.ArgKind, given: Bool) -> Bool:
  match kk:
    case S.Opt{}:
      Bool.not(given)
    case S.Many{}:
      True{}
    case _other:
      False{}

# a flag's or an option's spelling: `--long`, else `-s`, then its value
# mark; its name when it has neither
def spelled(+short: String, +long: String, +name: String, +mark: String) -> String:
  Bool.pick(String, String.is_empty(long),
    Bool.pick(String, String.is_empty(short), name, "-" ++ short ++ mark),
    "--" ++ long ++ mark)

# a positional's form: `<NAME>` when required, `[NAME]` otherwise
def pos_form(req: Bool, +nn: String) -> String:
  match req:
    case True{}:
      "<" ++ nn ++ ">"
    case False{}:
      "[" ++ nn ++ "]"

# an argument of this kind as an error names it
def form_of.kind(kk: S.ArgKind, +name: String, +sh: String, +lo: String, req: Bool) -> String:
  match kk:
    case S.Flag{}:
      spelled(sh, lo, name, "")
    case S.Opt{}:
      spelled(sh, lo, name, " <" ++ String.to_upper(name) ++ ">")
    case S.Many{}:
      spelled(sh, lo, name, " <" ++ String.to_upper(name) ++ ">...")
    case S.Pos{}:
      pos_form(req, String.to_upper(name))
    case S.Rest{}:
      pos_form(req, String.to_upper(name)) ++ "..."

# an argument's display form
def form_of(aa: S.Arg) -> String:
  S.Arg{+name, short, long, kind, _h, req, _d, _c} = aa
  form_of.kind(kind, name, S.text.of(short, ""), S.text.of(long, ""), req)

# a found argument's display form, else the name the error carries
def named(found: Maybe<&2, S.Arg>, +name: String) -> String:
  match found:
    case None{}:
      name
    case Some{aa}:
      form_of(aa)

# a positional's mark: `<NAME>` when required, `[NAME]` otherwise
def mark.req(req: Bool, +nn: String) -> String:
  match req:
    case True{}:
      " <" ++ nn ++ ">"
    case False{}:
      " [" ++ nn ++ "]"

# `...` after a rest positional
def mark.rest(kk: S.ArgKind) -> String:
  match kk:
    case S.Rest{}:
      "..."
    case S.Pos{}:
      ""
    case S.Flag{}:
      ""
    case S.Opt{}:
      ""
    case S.Many{}:
      ""

# a positional as a usage line names it
def mark(aa: S.Arg) -> String:
  S.Arg{+name, _s, _l, kind, _h, required, _d, _c} = aa
  mark.req(required, String.to_upper(name)) ++ mark.rest(kind)

# the names of some arguments
def arg_names(args: List<&2, S.Arg>) -> List<&2, String>:
  match args:
    case Nil{}:
      []
    case Con{hh, tt}:
      S.Arg{name, _s, _l, _k, _h, _r, _d, _c} = hh
      name <> arg_names(tt)

# the short spellings of some arguments, of those that have one
def arg_shorts(args: List<&2, S.Arg>) -> List<&2, String>:
  match args:
    case Nil{}:
      []
    case Con{hh, tt}:
      S.Arg{_n, short, _l, _k, _h, _r, _d, _c} = hh
      K.spelled.add(short, arg_shorts(tt))

# the long spellings of some arguments, of those that have one
def arg_longs(args: List<&2, S.Arg>) -> List<&2, String>:
  match args:
    case Nil{}:
      []
    case Con{hh, tt}:
      S.Arg{_n, _s, long, _k, _h, _r, _d, _c} = hh
      K.spelled.add(long, arg_longs(tt))

# a report of a default that is outside nonempty choices
def off_choice(
  +path: List<&2, String>,
  +name: String,
  +cs: List<&2, String>,
  dflt: Maybe<&2, String>
) -> List<&2, K.SpecErr>:
  match dflt:
    case None{}:
      []
    case Some{+vv}:
      K.one(Bool.and(Bool.not(List.is_empty(&2, String, cs)), Bool.not(List.contains(~String, ~String.eq, cs, vv))),
        K.DefaultNotChoice{path, name, vv})

# the reports about one argument of a command, against the arguments before
# it, then `after`: its name, short and long spellings where an earlier one
# has them, and its default
def arg_reports(
  +path: List<&2, String>,
  +before: List<&2, S.Arg>,
  aa: S.Arg,
  after: List<&2, K.SpecErr>
) -> List<&2, K.SpecErr>:
  S.Arg{+name, +short, +long, _k, _h, _r, S.Fallback{_e, dflt}, +cs} = aa
  K.both(K.one(List.contains(~String, ~String.eq, arg_names(before), name), K.SameName{path, name}),
    K.both(K.one(K.spelled.seen(short, arg_shorts(before)), K.SameShort{path, S.text.of(short, "")}),
      K.both(K.one(K.spelled.seen(long, arg_longs(before)), K.SameLong{path, S.text.of(long, "")}),
        K.both(off_choice(path, name, cs, dflt), after))))

# the reports about each argument, in spec order, given those before them
def args_reports(
  args: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> List<&2, K.SpecErr>:
  match args:
    case Nil{}:
      []
    case Con{+hh, tt}:
      arg_reports(path, before, hh, args_reports(tt, path, hh <> before))

# whether one of some arguments is optional
def any_optional(args: List<&2, S.Arg>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{hh, tt}:
      S.Arg{_n, _s, _l, _k, _h, required, _d, _c} = hh
      Bool.or(any_optional(tt), Bool.not(required))

# the reports about each positional, in spec order, given those before them: a
# rest positional with one after it, and a required one after an optional one
def pos_reports(
  pos: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> List<&2, K.SpecErr>:
  match pos:
    case Nil{}:
      []
    case Con{+hh, +tt}:
      S.Arg{+name, _s, _l, kind, _h, required, _d, _c} = hh
      K.both(K.one(Bool.and(S.rest.is.kind(kind), Bool.not(List.is_empty(&2, S.Arg, tt))), K.RestNotLast{path, name}),
        K.both(K.one(Bool.and(required, any_optional(before)), K.RequiredAfterOptional{path, name}),
          pos_reports(tt, path, hh <> before)))

# the names of some subcommands
def sub_names(subs: List<&2, S.Sub>) -> List<&2, String>:
  match subs:
    case Nil{}:
      []
    case Con{hh, tt}:
      S.Sub{name, _a, _g, _c} = hh
      name <> sub_names(tt)

# the reports about each subcommand, in spec order, given those before them:
# a name an earlier one has, and the name `help`
def sub_reports(
  subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +before: List<&2, S.Sub>
) -> List<&2, K.SpecErr>:
  match subs:
    case Nil{}:
      []
    case Con{+hh, tt}:
      S.Sub{+name, _a, _g, _c} = hh
      K.both(K.one(List.contains(~String, ~String.eq, sub_names(before), name), K.SameSub{path, name}),
        K.both(K.one(String.eq(name, "help"), K.HelpSub{path}), sub_reports(tt, path, hh <> before)))

# one command's reports, at its path: its arguments', its positionals', its
# subcommands'
def cmd_reports(
  +path: List<&2, String>,
  +args: List<&2, S.Arg>,
  subs: List<&2, S.Sub>
) -> List<&2, K.SpecErr>:
  K.both(args_reports(args, path, []), K.both(pos_reports(S.pos_of(args), path, []), sub_reports(subs, path, [])))

# the reports of every command under some subcommands of the command at
# `path`, depth first, each at its own path
def below(subs: List<&2, S.Sub>, +path: List<&2, String>) -> List<&2, K.SpecErr>:
  match subs:
    case Nil{}:
      []
    case Con{hh, tt}:
      S.Sub{+name, _a, +args, +kids} = hh
      +here = List.append(&2, String, path, [name])
      K.both(cmd_reports(here, args, kids), K.both(below(kids, here), below(tt, path)))

# whether `vv` is what is left of the word `wd` once some chars, maybe none, are
# dropped from its front
def ends(wd: String, +vv: String) -> Bool:
  match wd:
    case SNil{}:
      String.eq(vv, "")
    case SCon{+hh, +tt}:
      Bool.or(String.eq(vv, SCon{hh, tt}), ends(tt, vv))

# whether `vv` is a piece of one of the words: what is left of it once some
# chars are dropped from its front
def piece(ws: List<&2, String>, +vv: String) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+ww, tt}:
      Bool.or(ends(ww, vv), piece(tt, vv))

# whether a default is `vv`
def default_is(dd: Maybe<&2, String>, +vv: String) -> Bool:
  match dd:
    case None{}:
      False{}
    case Some{dv}:
      String.eq(dv, vv)

# whether `vv` is the default of one of `args` named `name`
def is_default(args: List<&2, S.Arg>, +name: String, +vv: String) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{hh, tt}:
      S.Arg{nn, _s, _l, _k, _h, _r, S.Fallback{_e, dd}, _c} = hh
      Bool.or(Bool.and(String.eq(nn, name), default_is(dd, vv)), is_default(tt, name, vv))

# whether a binding's value is `true`, which a flag binds, a piece of one of
# the words, or the default of one of `args` of its name
def given(+ws: List<&2, String>, +args: List<&2, S.Arg>, bb: S.Bind) -> Bool:
  S.Bind{+name, +vv} = bb
  Bool.or(String.eq(vv, "true"), Bool.or(piece(ws, vv), is_default(args, name, vv)))
