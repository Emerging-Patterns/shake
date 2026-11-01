import Base
import ../main.bend as Shake
import ./defs/HelpPages.bend as D1

# LAW: `help` renders the page of the command a path reaches from the root
law help_page:
  for spec: Shake.Cli
  for +path: List<&2, String>
  {Shake.help(spec, path) == D1.page(D1.reach(path, D1.root(spec))) : String}
