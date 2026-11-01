# the env value check over no arguments finds nothing
import Base
import ../../src/cli.bend as S
import ../../laws/EnvValueOutsideChoicesFails.bend as L1

def L1.bad_args_nil(args, bs):
  match args:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      match hh:
        case S.Arg{_n, _s, _l, _k, _h, _r, fb, _c}:
          match fb:
            case S.Fallback{ev, _d}:
              match ev:
                case None{}:
                  L1.bad_args_nil(tt, bs)
                case Some{_var}:
                  L1.bad_args_nil(tt, bs)
