# proofs of laws/ErrTextEmptyForRequests.bend
import Base
import ../src/cli.bend as S
import ../laws/ErrTextEmptyForRequests.bend as Laws

def Laws.err_text_help(_spec, _path):
  {==}

def Laws.err_text_version(_spec):
  {==}

def Laws.err_text_iff(spec, err):
  match spec err:
    case S.Cli{_n, _a, _v, _g, _s} S.UnknownFlag{_at, _flag}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Missing{_at, _name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NoValue{_at, _name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.BadValue{_at, _name, _value}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedHelp{_path}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Unexpected{_at, _arg}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Repeated{_at, _name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedVersion{}:
      {==}
