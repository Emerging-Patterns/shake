# proofs of laws/ArgvDropsProgram.bend
import Base
import ../src/args.bend as Args
import ../laws/ArgvDropsProgram.bend as Laws

def Laws.copy_keeps(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      ih = Equal.sym(List<&1, String>, Laws.down(Args.copy(tt)), tt, Laws.copy_keeps(tt))
      %ih : {hh <> _ == hh <> tt : List<&1, String>}
      {==}

def Laws.words_keeps(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{_hh, tt}:
      Laws.copy_keeps(tt)
