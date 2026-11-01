# When a word exactly `--` reaches `parse` where an option could stand, it
# binds nothing and every later word is read as a plain word bound to a
# positional, whatever its shape.
#
# also rests on: laws/RawBinds.bend, laws/RawNext.bend, laws/RawNoPos.bend,
# laws/RawRefused.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free and before `--`, a
# word `--` binds nothing and leaves it free after `--`
law dd_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  {S.parse.walk(List.append(&2, String, pre, ["--"]), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, True{}, seen} : S.St}
