# For every Matched `m` and name: `get(m, name)` is `Some` of the value of the
# last binding of that name that `m`'s command made, or `None` when it made
# none; `get_all(m, name)` is the values of every binding of that name that
# `m`'s command made, in binding order; `on(m, name)` is true exactly when
# `get(m, name)` is `Some{"true"}`. A command's Matched reads only its own
# bindings: the subcommand selected under it changes none of these.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: `get_all` of two lists of bindings is the first's values, then the
# second's
law get_all_append:
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  {Shake.get_all(S.Leaf{List.append(&2, S.Bind, bs, cs)}, name)
    == List.append(&2, String, Shake.get_all(S.Leaf{bs}, name),
      Shake.get_all(S.Leaf{cs}, name)) : List<&2, String>}

# LAW: one binding of a name gives `get_all` its value
law get_all_hit:
  for +name: String
  for +vv: String
  {Shake.get_all(S.Leaf{[S.Bind{name, vv}]}, name) == [vv] : List<&2, String>}

# LAW: one binding of another name gives `get_all` nothing
law get_all_miss:
  for +other: String
  for +name: String
  for +vv: String
  for differ: {String.eq(other, name) == False{} : Bool}
  {Shake.get_all(S.Leaf{[S.Bind{other, vv}]}, name) == [] : List<&2, String>}

# LAW: `get` is the value of the last binding of the name
law get_last:
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  for +vv: String
  for after: {Shake.get_all(S.Leaf{cs}, name) == [] : List<&2, String>}
  {Shake.get(S.Leaf{List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs)}, name)
    == Some{vv} : Maybe<&2, String>}

# LAW: `get` is None when nothing binds the name
law get_none:
  for +bs: List<&2, S.Bind>
  for +name: String
  for none: {Shake.get_all(S.Leaf{bs}, name) == [] : List<&2, String>}
  {Shake.get(S.Leaf{bs}, name) == None{} : Maybe<&2, String>}

# LAW: a flag is on exactly when `get` reads Some "true"
law on_some:
  for +found: Shake.Matched
  for +name: String
  for +vv: String
  for h_get: {Shake.get(found, name) == Some{vv} : Maybe<&2, String>}
  {Shake.on(found, name) == String.eq(vv, "true") : Bool}

# LAW: nothing is on that nothing bound
law on_none:
  for +found: Shake.Matched
  for +name: String
  for h_get: {Shake.get(found, name) == None{} : Maybe<&2, String>}
  {Shake.on(found, name) == False{} : Bool}

# LAW: a command's `get_all` reads only its own bindings: the subcommand
# selected under it changes nothing
law get_all_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  {Shake.get_all(S.Node{bs, nn, below}, name) == Shake.get_all(S.Leaf{bs}, name) : List<&2, String>}

# LAW: a command's `get` reads only its own bindings
law get_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  {Shake.get(S.Node{bs, nn, below}, name) == Shake.get(S.Leaf{bs}, name) : Maybe<&2, String>}
