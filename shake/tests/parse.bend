# shake/parse: flags, options, positionals, nested commands, `--`
import Base
import ../main.bend as Shake
import ../sample.bend as Sample
import ../check.bend as Check

# parse argv against the sample Cli
def run(av: List<&2, String>) -> String:
  Shake.show(Shake.parse(Sample.spec(), av))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("flag long", run(["--verbose", "greet"]),
      "ok greet | verbose=true name=world")
    Check.eq_str("flag short", run(["-v", "greet"]),
      "ok greet | verbose=true name=world")
    Check.eq_str("opt long value", run(["greet", "--name", "Ada"]),
      "ok greet | name=Ada")
    Check.eq_str("opt equals", run(["greet", "--name=Ada"]),
      "ok greet | name=Ada")
    Check.eq_str("opt short value", run(["greet", "-n", "Ada"]),
      "ok greet | name=Ada")
    Check.eq_str("opt short glued", run(["greet", "-nAda"]),
      "ok greet | name=Ada")
    Check.eq_str("positional", run(["greet", "Ada"]),
      "ok greet | who=Ada name=world")
    Check.eq_str("default name", run(["greet"]),
      "ok greet | name=world")
    Check.eq_str("required positionals", run(["add", "2", "3"]),
      "ok add | a=2 b=3")
    Check.eq_str("nested command", run(["add", "2", "3", "more"]),
      "ok add/more | a=2 b=3")
    Check.eq_str("passthrough after --", run(["greet", "--", "--name"]),
      "ok greet | who=--name name=world")

#|ok flag long
#|ok flag short
#|ok opt long value
#|ok opt equals
#|ok opt short value
#|ok opt short glued
#|ok positional
#|ok default name
#|ok required positionals
#|ok nested command
#|ok passthrough after --
