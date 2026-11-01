# whether a pending positional blocks a subcommand
import Base
import ../../src/cli.bend as S

# whether a pending positional blocks a subcommand: required, with no
# default, and not a rest
def blocks(aa: S.Arg) -> Bool:
  S.Arg{_n, _s, _l, kind, _h, req, S.Fallback{_e, dflt}, _c} = aa
  Bool.and(Bool.not(S.rest.is.kind(kind)), Bool.and(req, Maybe.is_none(&2, String, dflt)))
