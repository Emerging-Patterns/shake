# proofs of laws/VersionOfNamesRelease.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/VersionOfNamesRelease.bend as Laws

def Laws.version_of_some(_name, _about, _ver, _args, _subs):
  {==}

def Laws.version_of_none(_name, _about, _args, _subs, err):
  match err:
    case S.NeedVersion{}:
      {==}
    case S.UnknownFlag{_at, _word}:
      {==}
    case S.Missing{_at, _name}:
      {==}
    case S.NoValue{_at, _name}:
      {==}
    case S.BadValue{_at, _name, _value}:
      {==}
    case S.NeedHelp{_path}:
      {==}
    case S.Unexpected{_at, _arg}:
      {==}
    case S.Repeated{_at, _name}:
      {==}

def Laws.version_of_other(_spec, err, h_err):
  match err:
    case S.NeedVersion{}:
      Empty.absurd({Shake.version_of(_spec, S.NeedVersion{}) == None{} : Maybe<&2, String>}, Walk.wk.true_false(h_err))
    case S.UnknownFlag{_at, _word}:
      {==}
    case S.Missing{_at, _name}:
      {==}
    case S.NoValue{_at, _name}:
      {==}
    case S.BadValue{_at, _name, _value}:
      {==}
    case S.NeedHelp{_path}:
      {==}
    case S.Unexpected{_at, _arg}:
      {==}
    case S.Repeated{_at, _name}:
      {==}
