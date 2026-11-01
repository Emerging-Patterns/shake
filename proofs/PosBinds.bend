# proofs of laws/PosBinds.bend
import Base
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ../laws/Kept.bend as L1
import ../laws/PosBinds.bend as Laws
import ./lemmas/BindingsKept.bend as M1
import ./lemmas/WalkSteps.bend as M2

def Laws.pos_binds(
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
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  found,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{},
    seen} : S.St}
  L1.kept(spec, pre, more, tok, st, args, up, path, name, tok, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step(tok, st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
        S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
          S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
      M2.pos.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs, rest, h_dd, h_help,
        h_dash, h_sub, h_ok)),
    h_done)
