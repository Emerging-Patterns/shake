import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ./defs/ValuesAtPath.bend as D1

# LAW: when the words `mid`, read where the words before them leave the
# walker, stay in the command at `path` and put bindings `xs` in front of the
# bindings `bs` it made, and the parse succeeds, `get_all` of a name in that
# command's Matched reads its values in `bs`, then its values in `xs`, both in
# the order given, then any it bound after, whatever follows (a lemma)
law kept_all:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +mid: List<&2, String>
  for +more: List<&2, String>
  for +st: S.St
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +xs: List<&2, S.Bind>
  for +bs: List<&2, S.Bind>
  for +name: String
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_mid: {Grow.view(S.parse.walk(mid, st)) == Grow.View{args, up, path, List.append(&2, S.Bind, xs, bs)}
    : Grow.View}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, mid), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name),
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, xs), name), after))}
    : Maybe<&2, List<&2, String>>}
