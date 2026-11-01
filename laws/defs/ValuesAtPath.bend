# the values a Matched holds for a name at a command path
import Base
import ../../main.bend as Shake

# `get_all` of the command a path reaches in a Matched, when it reaches one
def all_at.go(mm: Maybe<&2, Shake.Matched>, +name: String) -> Maybe<&2, List<&2, String>>:
  match mm:
    case None{}:
      None{}
    case Some{found}:
      Some{Shake.get_all(found, name)}

# `get_all` of the command at `path` in a Matched
def all_at(found: Shake.Matched, path: List<&2, String>, +name: String) -> Maybe<&2, List<&2, String>>:
  all_at.go(Shake.at(found, path), name)
