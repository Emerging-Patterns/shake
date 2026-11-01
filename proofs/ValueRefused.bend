# proofs of laws/ValueRefused.bend
import Base
import ../src/cli.bend as S
import ../laws/Refused.bend as L1
import ../laws/ValueRefused.bend as Laws
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1

# an option's value that is not flag-shaped and is not allowed fails the step
def value_refused.step(
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
  h_flag: {S.looks_flag(tok) == False{} : Bool},
  h_bad: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == False{} : Bool}
) -> {D1.dead_of(S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(Bool, S.looks_flag(tok), False{}, h_flag)
  %e1 : {D1.dead_of(S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, name)), tok), False{}, h_bad)
  %e2 : {D1.dead_of(S.parse.take_choice(_, name, tok, args, up, subs, path, bs, pos, raw, seen))
    == Some{S.BadValue{path, name, tok}} : Maybe<&2, S.ParseErr>}
  {==}

def Laws.value_refused(spec, pre, more, tok, name, args, up, subs, path, bs, pos, raw, seen, h_at, h_flag, h_bad):
  L1.refused(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen},
    S.BadValue{path, name, tok}, h_at,
    value_refused.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag, h_bad))
