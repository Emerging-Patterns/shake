# For every well-formed spec and word list, when `parse` succeeds, every
# binding in the Matched of each command on the selected path is `true` for a
# flag given while that command was current, a value-carrying piece of the
# words given while that command was current (a plain word bound to a
# positional, the value part of an option word, or the word after an option),
# bound verbatim under the name of the argument it was given for, or the
# default of an argument of that command that the words did not bind. One word
# adds at most one binding other than `true` to the current command, and a
# word read while the parse can still succeed is never ignored: it binds a
# value, sets a flag, enters a subcommand, waits for an option's value,
# switches to positionals, starts a help path, or fails.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ./defs/ArgumentLists.bend as D1

# whether every binding is given
def all_given(bs: List<&2, S.Bind>, +ws: List<&2, String>, +args: List<&2, S.Arg>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      Bool.and(D1.given(ws, args, hh), all_given(tt, ws, args))

# whether every binding of a command's own Matched is given, when there is one
def given_at.go(mm: Maybe<&2, Shake.Matched>, +ws: List<&2, String>, +args: List<&2, S.Arg>) -> Maybe<&2, Bool>:
  match mm:
    case None{}:
      None{}
    case Some{found}:
      Some{all_given(S.own(found), ws, args)}

# whether every binding of the command at `path` in a Matched is given
def given_at(
  found: Shake.Matched,
  path: List<&2, String>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>
) -> Maybe<&2, Bool>:
  given_at.go(Shake.at(found, path), ws, args)

# LAW: when the parse succeeds, every binding in the Matched of a command on
# the selected path is `true`, which a flag binds, a piece of one of the words,
# verbatim, or the default of one of that command's arguments: no value is
# invented, cut short or changed
law values_given:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +args: List<&2, S.Arg>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for +h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  {given_at(found, path, ws, args) == Some{True{}} : Maybe<&2, Bool>}

# whether one of `args` is named `name`
def has_arg(args: List<&2, S.Arg>, +name: String) -> Bool:
  match args:
    case Nil{}:
      False{}
    case Con{hh, tt}:
      S.Arg{nn, _s, _l, _k, _h, _r, _d, _c} = hh
      Bool.or(String.eq(nn, name), has_arg(tt, name))

# whether a binding is named after one of `args` and is given: `true`, a
# piece of one of the words, or the default of one of `args` of its name
def named_given(+ws: List<&2, String>, +args: List<&2, S.Arg>, bb: S.Bind) -> Bool:
  S.Bind{+name, +vv} = bb
  Bool.and(has_arg(args, name), D1.given(ws, args, S.Bind{name, vv}))

# whether every binding is named and given
def all_named(bs: List<&2, S.Bind>, +ws: List<&2, String>, +args: List<&2, S.Arg>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      Bool.and(named_given(ws, args, hh), all_named(tt, ws, args))

# whether every binding of a command's own Matched is named and given, when
# there is one
def named_at.go(mm: Maybe<&2, Shake.Matched>, +ws: List<&2, String>, +args: List<&2, S.Arg>) -> Maybe<&2, Bool>:
  match mm:
    case None{}:
      None{}
    case Some{found}:
      Some{all_named(S.own(found), ws, args)}

# whether every binding of the command at `path` in a Matched is named and
# given
def named_at(
  found: Shake.Matched,
  path: List<&2, String>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>
) -> Maybe<&2, Bool>:
  named_at.go(Shake.at(found, path), ws, args)

# LAW: when the parse succeeds, every binding in the Matched of a command on
# the selected path is named after one of that command's arguments, and is
# `true`, which a flag binds, a piece of the words read while that command
# was current (`mid`: from the word that selected it, or the start, to the
# word that selects a subcommand under it, or the end), verbatim, or the
# default of one of its arguments
law values_here:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +mid: List<&2, String>
  for +post: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +args: List<&2, S.Arg>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, List.append(&2, String, pre, List.append(&2, String, mid, post))) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_pre: {Grow.view(S.parse.walk(pre, S.parse.start(spec))) == Grow.View{args, up, path, []} : Grow.View}
  for h_mid: {Grow.view(S.parse.walk(List.append(&2, String, pre, mid), S.parse.start(spec)))
    == Grow.View{args, up, path, bs} : Grow.View}
  for +h_fr: {Grow.gw.frame(S.parse.walk(List.append(&2, String, pre, List.append(&2, String, mid, post)),
      S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  {named_at(found, path, mid, args) == Some{True{}} : Maybe<&2, Bool>}

# a count, with one more when a value is not `true`
def valued.at(flag: Bool, nn: Nat) -> Nat:
  match flag:
    case True{}:
      nn
    case False{}:
      1n+nn

# how many bindings have a value other than `true`, the value a flag binds
def valued(bs: List<&2, S.Bind>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{hh, tt}:
      S.Bind{_n, vv} = hh
      valued.at(String.eq(vv, "true"), valued(tt))

# whether `aa` is at most `bb`
def nat_le(aa: Nat, bb: Nat) -> Bool:
  match aa:
    case 0n:
      True{}
    case 1n+pp:
      match bb:
        case 0n:
          False{}
        case 1n+qq:
          nat_le(pp, qq)

# a walker's bindings for its current command
def binds_of(st: S.St) -> List<&2, S.Bind>:
  S.St{_m, _a, _g, _s, _p, binds, _o, _r, _n} = st
  binds

# LAW: one word adds at most one binding to the current command other than
# `true`, which a flag binds: a word never binds two values, whatever the
# walker it is read by
law one_value_per_word:
  for +tok: String
  for +st: S.St
  {nat_le(valued(binds_of(S.parse.step(tok, st))), 1n+valued(binds_of(st))) == True{} : Bool}

# LAW: a word read by a walker that can still finish as a success changes it:
# it binds a value, sets a flag, enters a subcommand, waits for an option's
# value, switches to positionals, starts a help path, or fails. No word is
# ignored
law word_used:
  for +tok: String
  for +st: S.St
  for h_live: {Grow.gw.live(st) == True{} : Bool}
  for h_same: {S.parse.step(tok, st) == st : S.St}
  Empty
