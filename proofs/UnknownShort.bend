# proofs of laws/UnknownShort.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../laws/Refused.bend as L1
import ../laws/UnknownShort.bend as Laws
import ../laws/UnknownShortStep.bend as L2
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/ClusterEnd.bend as M1
import ./lemmas/FailedWalkThrough.bend as M2

# the first letter of a short cluster that no argument has fails the step
def unknown_short.step(
  +cc: Char,
  +rest: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool},
  h_dash: {Char.is_eq(cc, '-') == False{} : Bool},
  h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>},
  h_help: {S.short_help(SCon{cc, rest}, args, seen) == False{} : Bool}
) -> {D1.dead_of(S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
    seen})) == Some{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}
    : Maybe<&2, S.ParseErr>}:
  ee = Equal.sym(S.St, S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos,
      False{}, seen}), S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc,
          rest}}}, args, up, subs, path, bs, pos, False{}, seen},
    L2.unknown_short_step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_none, h_help))
  %ee : {D1.dead_of(_) == Some{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.unknown_short(
  spec,
  pre,
  more,
  cc,
  rest,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_dash,
  h_none,
  h_help,
  h_ver
):
  +er = {S.UnknownFlag{path, "-" ++ SCon{cc, rest}} : S.ParseErr}
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>,
    Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["-" ++ SCon{cc, rest}]), more)),
    Fail{S.version.err(spec, er)}, Fail{er},
    L1.refused(spec, pre, more, "-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{},
        seen}, er, h_at,
      unknown_short.step(cc, rest, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_none, h_help)),
    M2.fs.keep(spec, path, "-" ++ SCon{cc, rest}, h_ver))
