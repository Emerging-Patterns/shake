# proofs of laws/ChoiceRefused.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/ChoiceRefused.bend as Laws
import ../laws/Refused.bend as L1
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# a plain word outside the next positional's choices fails the step with
# BadValue
def choice_refused.step(
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
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>},
  h_bad: {S.allowed(cs, tok) == False{} : Bool}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
    req, dflt, cs} <> rest, False{}, seen})) == Some{S.BadValue{path, name, tok}}
    : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(S.St, S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind,
      hp, req, dflt, cs} <> rest, False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}),
    Walk.wk.word_step(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
        seen, h_dd, h_help, h_dash,
      h_sub))
  %e1 : {D1.dead_of(_) == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.allowed(cs, tok), False{}, h_bad)
  %e2 : {D1.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.choice_refused(
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
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_bad
):
  L1.refused(spec, pre, more, tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp,
      req, dflt, cs} <> rest, False{}, seen}, S.BadValue{path, name, tok}, h_at,
    choice_refused.step(tok, args, up, subs, path, bs, seen, name, sh, lo, kind, hp, req, dflt, cs,
      rest, h_dd, h_help, h_dash, h_sub, h_bad))
