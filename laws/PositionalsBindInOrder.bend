# Plain words that select no subcommand bind the current command's positionals
# in spec order, one word each; a plain word with no positional left is
# refused as `Unexpected{word}`.
#
# also rests on: laws/EnterStep.bend, laws/NoPosLeft.bend, laws/PosBinds.bend,
# laws/PosNext.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/ValuesAtPath.bend as D1

# LAW: the walk starts free at the root, with no path, no bindings, the root's
# arguments current and its positionals pending
law start_state:
  for +name: String
  for +about: String
  for +version: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  {S.parse.walk([], S.parse.start(Shake.app(name, about, version, args, subs)))
    == S.St{S.Free{}, args, [], subs, [], [], S.pos_of(args), False{}, False{}} : S.St}

# LAW: the positionals pending for a list of arguments are those of its first
# part, then those of the rest, in spec order
law pos_of_app:
  for xs: List<&2, S.Arg>
  for +ys: List<&2, S.Arg>
  {S.pos_of(List.append(&2, S.Arg, xs, ys)) == List.append(&2, S.Arg, S.pos_of(xs), S.pos_of(ys)) : List<&2, S.Arg>}

# LAW: a positional or rest positional is pending for itself
law pos_of_pos:
  for +aa: S.Arg
  for h_pos: {S.pos.is(aa) == True{} : Bool}
  {S.pos_of([aa]) == [aa] : List<&2, S.Arg>}

# LAW: a flag or an option is not pending as a positional
law pos_of_opt:
  for +aa: S.Arg
  for h_opt: {S.pos.is(aa) == False{} : Bool}
  {S.pos_of([aa]) == [] : List<&2, S.Arg>}

# LAW: once a positional of the current command is bound, a word `help`
# before `--` is a plain word like any other: with a positional pending whose
# choices allow it, and no subcommand named `help`, it binds that positional
law help_word_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, True{}} : S.St}
  for h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>}
  for h_ok: {S.allowed(cs, "help") == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, ["help"]), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}

# LAW: ... and when the parse succeeds, `get_all` of that positional in its
# command's Matched reads the values bound to it before, then `help`
law help_word_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, True{}} : S.St}
  for h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>}
  for h_ok: {S.allowed(cs, "help") == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["help"]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), "help" <> after)}
    : Maybe<&2, List<&2, String>>}
