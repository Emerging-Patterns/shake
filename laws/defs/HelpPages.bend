# help pages as help renders them: reaching one, its usage line, its root
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S

# the page a help walk reaches from `how`: each name that is a subcommand
# where it stands moves to it, and any other name is skipped
def reach(path: List<&2, String>, how: S.How) -> S.How:
  match path:
    case Nil{}:
      how
    case Con{+hh, tt}:
      reach(tt, S.help.step(how, hh))

# the root's page
def root(app: Shake.Cli) -> S.How:
  S.Cli{+name, about, version, args, subs} = app
  S.How{name, about, version, args, subs, name}

# the usage line of a page
def usage_line(how: S.How) -> String:
  S.How{_b, _a, version, +args, +subs, +usage} = how
  S.help.usage(usage, S.help.with(args, version), subs)

# a page as `help` renders it: its title, what it is about, its usage line
# (`usage_line`), its subcommands, its positionals and its options, the
# built-in flags after the command's own
def page(how: S.How) -> String:
  S.How{+bin, +about, +version, +args, +subs, +usage} = how
  S.help.page(S.title.go(bin, version), about, S.help.usage(usage, S.help.with(args, version), subs),
    S.help.with(args, version), subs)

# whether an error is an unknown option
def unknown.is(err: Shake.ParseErr) -> Bool:
  match err:
    case S.UnknownFlag{_at, _word}:
      True{}
    case _other:
      False{}
