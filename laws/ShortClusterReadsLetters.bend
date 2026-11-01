# A word that starts with `-`, is not `-` and does not start with `--` is a
# cluster of short options, read letter by letter: a letter that spells a flag
# binds it and the next letter goes on; a letter that spells an option takes
# the rest of the word as its value, after one `=` when the rest starts with
# it (verbatim, and possibly empty), or the next word when nothing is left; a
# letter no argument of the current command spells refuses the whole word as
# `UnknownFlag{word}`, except that a word `-h` may be a request for help
# (laws/HelpWordAsksForHelp.bend) and a word `-V` a request for the version
# (laws/VersionWordAsksForVersion.bend).
#
# also rests on: laws/LetterUnknown.bend, laws/LetterValue.bend,
# laws/LetterValueEq.bend
import Base
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1

# LAW: in a free walker before `--`, a word that starts with `-`, is not `-`
# and does not start with `--` is read as a cluster of short options, letter
# by letter, from the walker as it stood
law short_step:
  for +cc: Char
  for +rest: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_help: {S.short_help(SCon{cc, rest}, args, seen) == False{} : Bool}
  {S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.cluster(SCon{cc, rest}, "-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      False{}) : S.St}

# LAW: a letter that spells a flag not yet given, with no `=` after it, binds
# it, and the next letter goes on
law letter_flag:
  for +cc: Char
  for +rest: String
  for +orig: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_once: {S.bound(bs, nn) == False{} : Bool}
  for h_noeq: {String.starts_with(rest, "=") == False{} : Bool}
  {S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.cluster(rest, orig, S.St{S.Free{}, args, up, subs, path, S.Bind{nn, "true"} <> bs, pos, raw, seen}, False{})
    : S.St}

# LAW: a letter that spells an option taking a value now, last in its word,
# leaves the option waiting for the next word
law letter_value_next:
  for +cc: Char
  for +orig: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_kind: {D1.takes(kind, S.bound(bs, nn)) == True{} : Bool}
  {S.cluster(SCon{cc, SNil{}}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.St{S.Need{nn}, args, up, subs, path, bs, pos, raw, seen} : S.St}
