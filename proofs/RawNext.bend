# proofs of laws/RawNext.bend
import Base
import ../src/cli.bend as S
import ../laws/RawNext.bend as Laws
import ./lemmas/WalkSteps.bend as M1

def Laws.raw_next(
  spec,
  pre,
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
  h_at,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, True{},
    seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)), S.parse.step(tok, st),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}},
    M1.kept.stepped(spec, pre, tok, st, h_at),
    M1.pos.take(tok, args, up, subs, path, bs, True{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))
