# proofs of laws/ArgLineMark.bend
import Base
import ../src/cli.bend as S
import ../laws/ArgLineMark.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1

# a usage mark's brackets, as the law's mark writes them
def ha.wrap(req: Bool, +nn: String) -> {S.help.pos.wrap(req, nn) == D1.mark.req(req, nn) : String}:
  match req:
    case True{}:
      {==}
    case False{}:
      {==}

# a usage mark's dots, as the law's mark writes them
def ha.dots(kind: S.ArgKind) -> {S.help.pos.dots(S.rest.is.kind(kind)) == D1.mark.rest(kind) : String}:
  match kind:
    case S.Flag{}:
      {==}
    case S.Opt{}:
      {==}
    case S.Pos{}:
      {==}
    case S.Rest{}:
      {==}
    case S.Many{}:
      {==}

# a positional's usage hint is the law's mark
def ha.mark(
  +nn: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +fb: S.Fallback,
  +cs: List<&2, String>
) -> {S.help.pos.one(S.Arg{nn, sh, lo, kind, hp, req, fb, cs}) == D1.mark(S.Arg{nn, sh, lo, kind, hp, req, fb, cs})
    : String}:
  +up = String.to_upper(nn)
  Equal.trans(String, S.help.pos.wrap(req, up) ++ S.help.pos.dots(S.rest.is.kind(kind)),
    D1.mark.req(req, up) ++ S.help.pos.dots(S.rest.is.kind(kind)), D1.mark.req(req, up) ++ D1.mark.rest(kind),
    Equal.cong(String, String, xs => xs ++ S.help.pos.dots(S.rest.is.kind(kind)), S.help.pos.wrap(req, up),
      D1.mark.req(req, up), ha.wrap(req, up)),
    Equal.cong(String, String, xs => D1.mark.req(req, up) ++ xs, S.help.pos.dots(S.rest.is.kind(kind)),
      D1.mark.rest(kind), ha.dots(kind)))

def Laws.arg_line_mark(nn, sh, lo, kind, hp, req, fb, cs, ww):
  +aa = {S.Arg{nn, sh, lo, kind, hp, req, fb, cs} : S.Arg}
  Equal.cong(String, String, mm => "  " ++ S.help.pad(String.drop(mm, 1n), ww) ++ "  " ++ hp ++ S.help.extra(aa),
    S.help.pos.one(aa), D1.mark(aa), ha.mark(nn, sh, lo, kind, hp, req, fb, cs))
