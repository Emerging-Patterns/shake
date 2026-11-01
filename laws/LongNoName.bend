import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free, a word `--=...`,
# with nothing between `--` and `=`, fails the parse with UnknownFlag of the
# word, whatever follows
law long_no_name:
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
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for +h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for +h_empty: {String.is_empty(name) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.UnknownFlag{path, "--" ++ body}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
