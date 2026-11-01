# whether an error is a request for the version
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S

# whether an error is a request for the version
def version.is(err: Shake.ParseErr) -> Bool:
  match err:
    case S.NeedVersion{}:
      True{}
    case _other:
      False{}
