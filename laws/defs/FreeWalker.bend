# whether a walker or a mode is free to read an option
import Base
import ../../src/cli.bend as S

# whether a mode is free
def free.mode(mode: S.Mode) -> Bool:
  match mode:
    case S.Free{}:
      True{}
    case _other:
      False{}

# whether a walker is free
def free(st: S.St) -> Bool:
  S.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  free.mode(mode)
