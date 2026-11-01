# proofs of laws/HelpUnknown.bend
import Base
import ../src/cli.bend as S
import ../laws/HelpUnknown.bend as Laws
import ../laws/Refused.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# a word after `help` that names no subcommand where the path stands fails
# the step
def help_unknown.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, tok), None{}, h_sub)
  %ee : {D1.dead_of(S.parse.step.help_path(_, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.help_unknown(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at,
  h_sub
):
  L1.refused(spec, pre, more, tok, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen},
    S.Unexpected{path, tok}, h_at, help_unknown.step(tok, args, up, subs, path, bs, pos, raw, seen, h_sub))
