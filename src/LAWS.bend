# shake: the laws. The human states them; PROOF.bend must prove them. A law
# tagged with a SPEC.md ID proves that requirement, and its statement changes
# only when the row does. The untagged ones are lemmas for the proofs to come.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/args.bend as Args

# LAW: a word that starts `--` is flag-shaped
law looks_flag_long:
  for ss: String
  {S.looks_flag("--" ++ ss) == True{} : Bool}

# LAW: empty choices accept every value
law allowed_any:
  for vv: String
  {S.allowed([], vv) == True{} : Bool}

# LAW: `get` on a Matched with no bindings is ""
law get_nil:
  for name: String
  {S.get(S.Matched{[], []}, name) == "" : String}

# LAW: no flag is on in a Matched with no bindings
law on_nil:
  for name: String
  {S.on(S.Matched{[], []}, name) == False{} : Bool}

# LAW: copying a list of one word keeps the word
law copy_one:
  for +hh: String
  {Args.copy(hh <> Nil{}) == hh <> Nil{} : List<&2, String>}

# LAW: a request for help has no error text, for every spec and path
# SHAKE-ERR-1
law err_text_help:
  for spec: Shake.Cli
  for path: List<&2, String>
  {Shake.err_text(spec, S.NeedHelp{path}) == "" : String}

# LAW: the error text is empty exactly when the parse asked for help
# SHAKE-ERR-1
law err_text_iff:
  for +spec: Shake.Cli
  for +err: Shake.ParseErr
  {String.is_empty(Shake.err_text(spec, err))
    == Maybe.is_some(&2, List<&2, String>, Shake.help_path(err)) : Bool}

# LAW: a flag binding's hit keeps whatever list follows it (a lemma)
law hit_append:
  for bb: Bool
  for +vv: String
  for xs: List<&2, String>
  for ys: List<&2, String>
  {S.get_all.bind.hit(bb, vv, List.append(&2, String, xs, ys))
    == List.append(&2, String, S.get_all.bind.hit(bb, vv, xs), ys) : List<&2, String>}

# LAW: the values bound to a name in two lists of bindings are the first's
# then the second's (a lemma over the bindings alone)
law bind_values_append:
  for bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  {S.get_all.bind(List.append(&2, S.Bind, bs, cs), name)
    == List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(cs, name))
    : List<&2, String>}

# LAW: the last of a list that ends in `vv` is `vv`, whatever the default
law last_snoc:
  for xs: List<&2, String>
  for +vv: String
  for dflt: String
  {S.get.last(List.append(&2, String, xs, [vv]), dflt) == vv : String}

# LAW: `get_all` of two lists of bindings is the first's values, then the
# second's
# SHAKE-GET-1
law get_all_append:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  {Shake.get_all(S.Matched{path, List.append(&2, S.Bind, bs, cs)}, name)
    == List.append(&2, String, Shake.get_all(S.Matched{path, bs}, name),
      Shake.get_all(S.Matched{path, cs}, name)) : List<&2, String>}

# LAW: one binding of a name gives `get_all` its value
# SHAKE-GET-1
law get_all_hit:
  for +path: List<&2, String>
  for +name: String
  for +vv: String
  {Shake.get_all(S.Matched{path, [S.Bind{name, vv}]}, name) == [vv] : List<&2, String>}

# LAW: one binding of another name gives `get_all` nothing
# SHAKE-GET-1
law get_all_miss:
  for +path: List<&2, String>
  for +other: String
  for +name: String
  for +vv: String
  for differ: {String.eq(other, name) == False{} : Bool}
  {Shake.get_all(S.Matched{path, [S.Bind{other, vv}]}, name) == [] : List<&2, String>}

# LAW: `get` is the value of the last binding of the name
# SHAKE-GET-1
# SHAKE-PARSE-10
law get_last:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  for +vv: String
  for after: {Shake.get_all(S.Matched{path, cs}, name) == [] : List<&2, String>}
  {Shake.get(S.Matched{path, List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs)}, name)
    == vv : String}

# LAW: `get` is "" when nothing binds the name
# SHAKE-GET-1
law get_none:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +name: String
  for none: {Shake.get_all(S.Matched{path, bs}, name) == [] : List<&2, String>}
  {Shake.get(S.Matched{path, bs}, name) == "" : String}

# LAW: a flag is on exactly when `get` reads "true"
# SHAKE-GET-1
law on_get:
  for +found: Shake.Matched
  for +name: String
  {Shake.on(found, name) == String.eq(Shake.get(found, name), "true") : Bool}

# LAW: `path_of` is the selected path
# SHAKE-GET-1
law path_of_path:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  {Shake.path_of(S.Matched{path, bs}) == path : List<&2, String>}
