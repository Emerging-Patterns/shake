# shake/err: missing required, bad choices, unknown flags, help
import Base
import ../main.bend as Shake
import ../sample.bend as Sample
import ../check.bend as Check

# parse argv against the sample Cli
def run(av: List<&2, String>) -> String:
  Shake.show(Shake.parse(Sample.spec(), av))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("missing required", run(["add", "2"]),
      "err missing b")
    Check.eq_str("bad choice", run(["add", "2", "3", "--color", "purple"]),
      "err bad color purple")
    Check.eq_str("unknown long", run(["--nope"]),
      "err unknown --nope")
    Check.eq_str("unknown short", run(["-z"]),
      "err unknown -z")
    Check.eq_str("help root", run(["help"]),
      "err help ")
    Check.eq_str("help greet", run(["help", "greet"]),
      "err help greet")
    Check.eq_str("unexpected extra", run(["greet", "Ada", "extra"]),
      "err unexpected extra")

#|ok missing required
#|ok bad choice
#|ok unknown long
#|ok unknown short
#|ok help root
#|ok help greet
#|ok unexpected extra
