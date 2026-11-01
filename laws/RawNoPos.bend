import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: wherever the words before it leave the walker free after `--` with no
# positional left, any word fails the parse with Unexpected of the word,
# whatever follows
law raw_no_pos:
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
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [], True{}, seen} : S.St}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.Unexpected{path, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
