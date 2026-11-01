import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ./defs/ValuesAtPath.bend as D1

# LAW: when the words before `tok` reach a state where `tok` stays in the
# command at `path` and puts `Bind{name, vv}` in front of the bindings `bs` it
# made, and the parse succeeds, `get_all` of the name in that command's Matched
# reads the values bound to it before `tok`, then `vv`, then any bound after,
# whatever follows (a lemma: every binding row is its step fact through this,
# as every refusal row is through `refused`)
law kept:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +st: S.St
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +name: String
  for +vv: String
  for +bs: List<&2, S.Bind>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {Grow.view(S.parse.step(tok, st)) == Grow.View{args, up, path, S.Bind{name, vv} <> bs} : Grow.View}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), vv <> after)}
    : Maybe<&2, List<&2, String>>}
