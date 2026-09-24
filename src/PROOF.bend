# shake: the proofs. `bend src/PROOF.bend` is the gate.
import Base
import ../src/cli.bend as S
import ./LAWS.bend as Laws

def Laws.looks_flag_long(_ss):
  {==}

def Laws.allowed_any(_vv):
  {==}

def Laws.get_nil(_name):
  {==}

def Laws.on_nil(_name):
  {==}

def Laws.copy_one(_hh):
  {==}

def Laws.err_text_help(_spec, _path):
  {==}

def Laws.err_text_iff(spec, err):
  match spec err:
    case S.Cli{_n, _a, _v, _g, _s} S.UnknownFlag{_flag}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Missing{_name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.BadValue{_name, _value}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedHelp{_path}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Unexpected{_arg}:
      {==}
