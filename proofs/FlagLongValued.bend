# proofs of laws/FlagLongValued.bend
import Base
import ../src/cli.bend as S
import ../laws/FlagLongValued.bend as Laws
import ../laws/LongArgStep.bend as L1
import ../laws/Refused.bend as L2
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/WalkSteps.bend as M2

# a long option that gives a flag a value fails the step
def flag_long_valued.step(
  +body: String,
  +name: String,
  +vv: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_once: {S.bound(bs, nn) == False{} : Bool}
) -> {D1.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_long.found(S.by_long(args, name), name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen),
    L1.long_arg_step(body, name, Some{vv}, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {D1.dead_of(_) == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}, h_found)
  %e2 : {D1.dead_of(S.parse.take_long.found(_, name, Some{vv}, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen))
    == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, S.bound(bs, nn), False{}, h_once)
  %e3 : {D1.dead_of(S.parse.once(_, S.St{S.Dead{S.Unexpected{path, "--" ++ body}}, args, up, subs, path, bs, pos,
      False{}, seen}, nn, path)) == Some{S.Unexpected{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.flag_long_valued(
  spec,
  pre,
  more,
  body,
  name,
  vv,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  nn,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_found,
  h_once
):
  L2.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.Unexpected{path, "--" ++ body}, h_at,
    flag_long_valued.step(body, name, vv, args, up, subs, path, bs, pos, seen, nn, sh, lo, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_once))
