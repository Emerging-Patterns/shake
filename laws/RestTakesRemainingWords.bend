# A rest positional binds every remaining plain word that selects no
# subcommand, in order, each under the rest's name.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ./defs/ValuesAtPath.bend as D1

# whether a choices list allows every word
def all_allowed(+cs: List<&2, String>, ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, tt}:
      Bool.and(S.allowed(cs, ww), all_allowed(cs, tt))

# LAW: wherever the words before them leave the walker free before `--`, with
# only a rest positional left, plain words that name no subcommand and that its
# choices allow each bind it, in order, and the walker stays free with the
# rest still pending
law rest_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, seen}
    : S.St}
  for h_plain: {Walk.all_plain(fs) == True{} : Bool}
  for h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs),
      [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, Walk.wk.seen(fs, seen)} : S.St}

# LAW: wherever the words before them leave the walker free before `--`, with
# only a rest positional left, plain words that name no subcommand and that its
# choices allow are its values: when the parse succeeds, `get_all` of the rest
# in its command's Matched reads the values bound to it before, then the words,
# in order, whatever follows
law rest_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +more: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, seen}
    : S.St}
  for h_plain: {Walk.all_plain(fs) == True{} : Bool}
  for h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, fs), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before them leave the walker free after `--`, with
# only a rest positional left, words its choices allow, whatever their shape,
# each bind it, in order, and the walker stays free after `--` with the rest
# still pending
law rest_raw_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, seen}
    : S.St}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs),
      [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, Walk.wk.seen(fs, seen)} : S.St}

# LAW: wherever the words before them leave the walker free after `--`, with
# only a rest positional left, words its choices allow, whatever their shape,
# are its values: when the parse succeeds, `get_all` of the rest in its
# command's Matched reads the values bound to it before, then the words, in
# order, whatever follows
law rest_raw_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +more: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, seen}
    : S.St}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, fs), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}
