import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free before `--`, a plain
# word that names a subcommand of the current command, with nothing blocking
# it, selects it: the path gains the subcommand's name, its arguments become
# current with its positionals pending and no bindings of its own, and the
# command left keeps its arguments and bindings above it
law enter_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +name: String
  for +about: String
  for +next: List<&2, S.Arg>
  for +kids: List<&2, S.Sub>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {S.find_sub(subs, tok) == Some{S.Sub{name, about, next, kids}} : Maybe<&2, S.Sub>}
  for h_req: {S.parse.first_req(pos) == None{} : Maybe<&2, String>}
  {S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec))
    == S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
      False{}, False{}} : S.St}
