# proofs of laws/NoPosLeft.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/NoPosLeft.bend as Laws
import ../laws/Refused.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# a plain word with no positional left fails the step with Unexpected
def no_pos_left.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{},
    seen})) == Some{S.Unexpected{path, tok}}
    : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(S.St, S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, [], False{}),
    Walk.wk.word_step(tok, args, up, subs, path, bs, [], seen, h_dd, h_help, h_dash, h_sub))
  %ee : {D1.dead_of(_) == Some{S.Unexpected{path, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.no_pos_left(
  spec,
  pre,
  more,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub
):
  L1.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, [], False{}, seen},
      S.Unexpected{path, tok}, h_at,
    no_pos_left.step(tok, args, up, subs, path, bs, seen, h_dd, h_help, h_dash, h_sub))
