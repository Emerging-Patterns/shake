# For every Matched `m`: `sub_name(m)` is `Some` of the name of the subcommand
# selected under `m`'s command, or `None` when none was; `sub_of(m, name)` is
# that subcommand's Matched when its name is `name`, and `None` otherwise;
# `path_of(m)` is the names of the subcommands selected below `m`'s command,
# in order, so the whole selected path for the Matched `parse` answers; `at(m,
# [])` is `Some{m}`, and `at(m, name <> rest)` is `at` of `sub_of(m, name)`
# and `rest`, or `None` when `sub_of` is `None`.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: no subcommand was selected under a command with no Matched below it
law sub_name_leaf:
  for +bs: List<&2, S.Bind>
  {Shake.sub_name(S.Leaf{bs}) == None{} : Maybe<&2, String>}

# LAW: `sub_name` is the name of the subcommand selected
law sub_name_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  {Shake.sub_name(S.Node{bs, nn, below}) == Some{nn} : Maybe<&2, String>}

# LAW: `sub_of` the subcommand selected is its Matched
law sub_of_hit:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  {Shake.sub_of(S.Node{bs, nn, below}, nn) == Some{below} : Maybe<&2, Shake.Matched>}

# LAW: `sub_of` any other name is None
law sub_of_miss:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  for differ: {String.eq(nn, name) == False{} : Bool}
  {Shake.sub_of(S.Node{bs, nn, below}, name) == None{} : Maybe<&2, Shake.Matched>}

# LAW: `sub_of` is None when no subcommand was selected
law sub_of_leaf:
  for +bs: List<&2, S.Bind>
  for +name: String
  {Shake.sub_of(S.Leaf{bs}, name) == None{} : Maybe<&2, Shake.Matched>}

# LAW: no names are selected below a command with no subcommand selected
law path_of_leaf:
  for +bs: List<&2, S.Bind>
  {Shake.path_of(S.Leaf{bs}) == [] : List<&2, String>}

# LAW: the names selected below a command are its subcommand's name, then the
# names selected below that
law path_of_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  {Shake.path_of(S.Node{bs, nn, below}) == nn <> Shake.path_of(below) : List<&2, String>}

# `at` of what `sub_of` found, or None when it found nothing
def at.via(mm: Maybe<&2, Shake.Matched>, rest: List<&2, String>) -> Maybe<&2, Shake.Matched>:
  match mm:
    case None{}:
      None{}
    case Some{below}:
      Shake.at(below, rest)

# LAW: `at` an empty path is the Matched itself
law at_nil:
  for +found: Shake.Matched
  {Shake.at(found, []) == Some{found} : Maybe<&2, Shake.Matched>}

# LAW: `at` a path follows its first name with `sub_of`, then the rest
law at_cons:
  for +found: Shake.Matched
  for +name: String
  for +rest: List<&2, String>
  {Shake.at(found, name <> rest) == at.via(Shake.sub_of(found, name), rest) : Maybe<&2, Shake.Matched>}
