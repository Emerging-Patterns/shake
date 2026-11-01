import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: when the words end with an option still waiting for its value, the
# parse fails with Missing of the option
law value_absent:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(ws, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  {Shake.parse(spec, ws) == Fail{S.NoValue{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
