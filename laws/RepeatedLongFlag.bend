import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free, a long option that
# spells a flag already given fails the parse with Repeated of its name,
# whatever follows
law repeated_long_flag:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: S.Fallback
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_again: {S.bound(bs, nn) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.Repeated{path, nn}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
