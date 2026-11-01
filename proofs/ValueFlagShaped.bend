# proofs of laws/ValueFlagShaped.bend
import Base
import ../src/cli.bend as S
import ../laws/Refused.bend as L1
import ../laws/ValueFlagShaped.bend as Laws
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# a flag-shaped word where a value is wanted fails the step
def value_flag_shaped.step(
  +tok: String,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_flag: {S.looks_flag(tok) == True{} : Bool}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.NoValue{path, name}} : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(Bool, S.looks_flag(tok), True{}, h_flag)
  %ee : {D1.dead_of(S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.NoValue{path, name}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.value_flag_shaped(
  spec,
  pre,
  more,
  tok,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  h_at,
  h_flag
):
  L1.refused(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen},
    S.NoValue{path, name}, h_at, value_flag_shaped.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag))
