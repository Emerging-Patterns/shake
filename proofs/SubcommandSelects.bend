# proofs of laws/SubcommandSelects.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/SubcommandSelects.bend as Laws
import ../laws/defs/BlockingPositional.bend as D1

# a positional that does not block a subcommand is skipped: a rest, one not
# required, or one with a default
def blk.req(
  rk: Bool,
  req: Bool,
  +ev: Maybe<&2, String>,
  dflt: Maybe<&2, String>,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +cs: List<&2, String>,
  hh: {Bool.not(Bool.and(Bool.not(rk), Bool.and(req, Maybe.is_none(&2, String, dflt)))) == True{} : Bool}
) -> {S.parse.first_req.skip(rk, S.Arg{nm, sh, lo, kind, hp, req, S.Fallback{ev, dflt}, cs}) == None{} : Maybe<&2,
    String>}:
  match rk:
    case True{}:
      {==}
    case False{}:
      match req:
        case False{}:
          {==}
        case True{}:
          match dflt:
            case Some{_d}:
              {==}
            case None{}:
              Empty.absurd({S.parse.first_req.skip(False{}, S.Arg{nm, sh, lo, kind, hp, True{}, S.Fallback{ev,
                  None{}}, cs}) == None{}
                : Maybe<&2, String>}, Walk.wk.false_true(hh))

# the same, from the argument's kind
def blk.skip(
  +kind: S.ArgKind,
  +req: Bool,
  +dflt: S.Fallback,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +cs: List<&2, String>,
  hh: {Bool.not(D1.blocks(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs})) == True{} : Bool}
) -> {S.parse.first_req.skip(S.rest.is.kind(kind), S.Arg{nm, sh, lo, kind, hp, req, dflt, cs}) == None{}
    : Maybe<&2, String>}:
  match dflt:
    case S.Fallback{+ev, dm}:
      blk.req(S.rest.is.kind(kind), req, ev, dm, nm, sh, lo, kind, hp, cs, hh)

# past a positional that does not block, the first blocking one is the rest's
def blk.past(
  +kind: S.ArgKind,
  +req: Bool,
  +dflt: S.Fallback,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +cs: List<&2, String>,
  +tt: List<&2, S.Arg>,
  hh: {Bool.not(D1.blocks(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs})) == True{} : Bool}
) -> {S.parse.first_req(S.Arg{nm, sh, lo, kind, hp, req, dflt, cs} <> tt) == S.parse.first_req(tt) : Maybe<&2, String>}:
  ee = Equal.sym(Maybe<&2, String>,
    S.parse.first_req.skip(S.rest.is.kind(kind), S.Arg{nm, sh, lo, kind, hp, req, dflt, cs}), None{},
    blk.skip(kind, req, dflt, nm, sh, lo, hp, cs, hh))
  %ee : {S.parse.first_req.at(_, S.parse.first_req(tt)) == S.parse.first_req(tt) : Maybe<&2, String>}
  {==}

def Laws.none_blocking(pos, h_none):
  match pos:
    case Nil{}:
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+nm, +sh, +lo, +kind, +hp, +req, +dflt, +cs}:
          +ab = {S.Arg{nm, sh, lo, kind, hp, req, dflt, cs} : S.Arg}
          Equal.trans(Maybe<&2, String>, S.parse.first_req(ab <> tt), S.parse.first_req(tt), None{},
            blk.past(kind, req, dflt, nm, sh, lo, hp, cs, tt,
              Walk.wk.and_l(Bool.not(D1.blocks(ab)), Laws.none_block(tt), h_none)),
            Laws.none_blocking(tt, Walk.wk.and_r(Bool.not(D1.blocks(ab)), Laws.none_block(tt), h_none)))

def Laws.first_blocking(pa, nm, sh, lo, kind, hp, ev, cs, qa, h_pa, h_kind):
  match pa:
    case Nil{}:
      ee = Equal.sym(Bool, S.rest.is.kind(kind), False{}, h_kind)
      %ee : {S.parse.first_req.at(S.parse.first_req.skip(_, S.Arg{nm, sh, lo, kind, hp, True{}, S.Fallback{ev,
          None{}}, cs}),
          S.parse.first_req(qa)) == Some{nm} : Maybe<&2, String>}
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Arg{+n2, +s2, +l2, +k2, +h2, +r2, +d2, +c2}:
          +ab = {S.Arg{n2, s2, l2, k2, h2, r2, d2, c2} : S.Arg}
          +rest = List.append(&2, S.Arg, tt, S.Arg{nm, sh, lo, kind, hp, True{}, S.Fallback{ev, None{}}, cs} <> qa)
          Equal.trans(Maybe<&2, String>, S.parse.first_req(ab <> rest), S.parse.first_req(rest), Some{nm},
            blk.past(k2, r2, d2, n2, s2, l2, h2, c2, rest, Walk.wk.and_l(Bool.not(D1.blocks(ab)),
                Laws.none_block(tt), h_pa)),
            Laws.first_blocking(tt, nm, sh, lo, kind, hp, ev, cs, qa,
              Walk.wk.and_r(Bool.not(D1.blocks(ab)), Laws.none_block(tt), h_pa), h_kind))
