import Base
import ../main.bend as Shake
import ../src/check.bend as K

# the command path a report of `check` is at
def spec_path(err: K.SpecErr) -> List<&2, String>:
  match err:
    case K.RestNotLast{path, _n}:
      path
    case K.SameName{path, _n}:
      path
    case K.SameShort{path, _s}:
      path
    case K.SameLong{path, _l}:
      path
    case K.SameSub{path, _n}:
      path
    case K.HelpSub{path}:
      path
    case K.DefaultNotChoice{path, _n, _v}:
      path
    case K.RequiredAfterOptional{path, _n}:
      path

# LAW: the text of every report of `check` says first where it is: `spec: `
# at the root, else the command's path (a lemma for laws/CheckReportsSpecErrors.bend's reports)
law spec_err_where:
  for +err: K.SpecErr
  exs msg: String
  {Shake.spec_err_text(err) == K.at(spec_path(err)) ++ msg : String}
