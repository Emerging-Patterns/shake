# A plain word is never read as an option.
#
# also rests on: laws/HelpWalk.bend, laws/RawNext.bend, laws/ValueBinds.bend,
# laws/ValueRefused.bend
import Base
import ../src/cli.bend as S

# LAW: in a free walker before `--`, a word that does not start with `-`, other
# than a `help` that asks for help, is read as a subcommand or a positional,
# never as an option
law plain_word_step:
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_help: {Bool.and(String.eq(tok, "help"), Bool.not(seen)) == False{} : Bool}
  {S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen) : S.St}

# LAW: in a free walker before `--`, the word `-` is read as a subcommand or a
# positional, never as an option
law dash_word_step:
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  {S.parse.step("-", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.word.go(S.find_sub(subs, "-"), "-", args, up, subs, path, bs, pos, False{}, seen) : S.St}
