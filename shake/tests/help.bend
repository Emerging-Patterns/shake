# shake/help: generated usage for the root and a subcommand
import Base
import ../main.bend as Shake
import ../sample.bend as Sample
import ../check.bend as Check

# yes or no
def yn(b: Bool) -> String:
  Bool.pick(String, b, "yes", "no")

# the sample Cli's help at a path
def at(path: List<&2, String>) -> String:
  Shake.help(Sample.spec(), path)

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("root title",
      String.take(at([]), String.length("demo 0.1.0")), "demo 0.1.0")
    Check.eq_str("root usage",
      yn(String.contains(at([]), "Usage: demo [OPTIONS] [COMMAND]")), "yes")
    Check.eq_str("root commands",
      yn(String.contains(at([]), "greet")), "yes")
    Check.eq_str("root help command",
      yn(String.contains(at([]), "help")), "yes")
    Check.eq_str("root flag",
      yn(String.contains(at([]), "-v, --verbose")), "yes")
    Check.eq_str("greet usage",
      yn(String.contains(at(["greet"]), "Usage: demo greet")), "yes")
    Check.eq_str("greet default",
      yn(String.contains(at(["greet"]), "[default: world]")), "yes")
    Check.eq_str("add choices",
      yn(String.contains(at(["add"]), "[possible values: red, green, blue]")),
      "yes")

#|ok root title
#|ok root usage
#|ok root commands
#|ok root help command
#|ok root flag
#|ok greet usage
#|ok greet default
#|ok add choices
