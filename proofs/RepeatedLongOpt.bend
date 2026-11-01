# proofs of laws/RepeatedLongOpt.bend
import Base
import ../src/cli.bend as S
import ../laws/LongArgStep.bend as L1
import ../laws/OnceDead.bend as L2
import ../laws/Refused.bend as L3
import ../laws/RepeatedLongOpt.bend as Laws
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/FailedWalkerStays.bend as M2
import ./lemmas/WalkSteps.bend as M3

# a long option given again fails the step
def repeated_long_opt.step(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
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
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_name: {String.is_empty(name) == False{} : Bool},
  h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}} : Maybe<&2, S.Arg>},
  h_again: {S.bound(bs, nn) == True{} : Bool}
) -> {D1.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
    seen})) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
      seen),
    L1.long_arg_step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_name))
  %e1 : {D1.dead_of(_) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}}, h_found)
  %e2 : {D1.dead_of(S.parse.take_long.found(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, S.bound(bs, nn), True{}, h_again)
  %e3 : {D1.dead_of(S.parse.once(_, S.parse.take_opt(val, nn, args, up, subs, path, bs, pos, False{},
      seen), nn, path)) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}
  L2.once_dead(S.parse.take_opt(val, nn, args, up, subs, path, bs, pos, False{}, seen), nn, path)

def Laws.repeated_long_opt(
  spec,
  pre,
  more,
  body,
  name,
  val,
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
  h_again
):
  L3.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
      S.Repeated{path, nn}, h_at,
    repeated_long_opt.step(body, name, val, args, up, subs, path, bs, pos, seen, nn, sh, lo, hp, req, dflt, cs,
      h_dd, h_cut, h_name, h_found, h_again))
