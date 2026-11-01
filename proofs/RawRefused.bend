# proofs of laws/RawRefused.bend
import Base
import ../src/cli.bend as S
import ../laws/RawRefused.bend as Laws
import ../laws/Refused.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# after `--`, a word the next positional's choices refuse fails the step
def raw_refused.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_bad: {S.allowed(cs, tok) == False{} : Bool}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
    req, dflt, cs} <> rest, True{}, seen})) == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}:
  e2 = Equal.sym(Bool, S.allowed(cs, tok), False{}, h_bad)
  %e2 : {D1.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.raw_refused(
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
  h_at,
  h_bad
):
  L1.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req,
      dflt, cs} <> rest, True{}, seen}, S.BadValue{path, name, tok}, h_at,
    raw_refused.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs, rest, h_bad))
