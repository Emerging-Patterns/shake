# proofs of laws/EnterMissing.bend
import Base
import ../src/cli.bend as S
import ../laws/EnterMissing.bend as Laws
import ../laws/Refused.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/WalkSteps.bend as M2

# a blocking positional: the word fails the step with Missing of it
def enter.miss(
  +pos: List<&2, S.Arg>,
  +sub: S.Sub,
  +nm: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_req: {S.parse.first_req(pos) == Some{nm} : Maybe<&2, String>}
) -> {D1.dead_of(S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Missing{path, nm}} : Maybe<&2, S.ParseErr>}:
  er = Equal.sym(Maybe<&2, String>, S.parse.first_req(pos), Some{nm}, h_req)
  %er : {D1.dead_of(S.parse.enter_or(_, sub, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Missing{path, nm}} : Maybe<&2, S.ParseErr>}
  {==}

# a step equal to a failed walker fails the same way
def enter.dead(
  +tok: String,
  +st: S.St,
  +st2: S.St,
  +err: S.ParseErr,
  ee: {st2 == S.parse.step(tok, st) : S.St},
  hd: {D1.dead_of(st2) == Some{err} : Maybe<&2, S.ParseErr>}
) -> {D1.dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}:
  %ee : {D1.dead_of(_) == Some{err} : Maybe<&2, S.ParseErr>}
  hd

def Laws.enter_missing(
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
  seen,
  sub,
  nm,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_req
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e1 = Equal.sym(S.St, S.parse.step(tok, st),
    S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
    Equal.trans(S.St, S.parse.step(tok, st),
      S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen),
      S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
      M2.enter.word(tok, args, up, subs, path, bs, pos, seen, h_dd, h_help, h_dash),
      M2.enter.go(tok, args, up, subs, path, bs, pos, seen, sub, h_sub)))
  L1.refused(spec, pre, more, tok, st, S.Missing{path, nm}, h_at,
    enter.dead(tok, st, S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen),
      S.Missing{path, nm}, e1, enter.miss(pos, sub, nm, args, up, subs, path, bs, seen, h_req)))
