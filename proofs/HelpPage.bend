# proofs of laws/HelpPage.bend
import Base
import ../src/cli.bend as S
import ../laws/HelpPage.bend as Laws
import ../laws/defs/HelpPages.bend as D1

# the help walk renders the page it reaches
def hl.go(
  path: List<&2, String>,
  how: S.How
) -> {S.help.go(path, how) == D1.page(D1.reach(path, how)) : String}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, _g, _s, _u}:
          {==}
    case Con{+hh, tt}:
      hl.go(tt, S.help.step(how, hh))

def Laws.help_page(spec, path):
  match spec:
    case S.Cli{+name, +about, +version, +args, +subs}:
      hl.go(path, S.How{name, about, version, args, subs, name})
