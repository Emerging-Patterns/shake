import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/ValuesAtPath.bend as D1

# LAW: wherever the words before it leave an option waiting for its value, a
# word that is not flag-shaped and that the option's choices allow is its
# value: when the parse succeeds, `get_all` of the option reads the values
# given it before, then the word, whatever follows
law value_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_flag: {S.looks_flag(tok) == False{} : Bool}
  for h_ok: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {D1.all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), tok <> after)}
    : Maybe<&2, List<&2, String>>}
