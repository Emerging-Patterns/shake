import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free after `--` with a
# positional next whose choices do not allow it, any word fails the parse
# with BadValue, whatever follows
law raw_refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
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
      True{}, seen} : S.St}
  for h_bad: {S.allowed(cs, tok) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.BadValue{path, name, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
