# shake: the laws. The human states them; PROOF.bend must prove them. A law
# tagged with a SPEC.md ID proves that requirement, and its statement changes
# only when the row does. The untagged ones are lemmas for the proofs to come.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/args.bend as Args

# a `&2` word list read back as the `&1` list IO.args answers
def down(ys: List<&2, String>) -> List<&1, String>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+hh, tt}:
      hh <> down(tt)

# the error a walker has failed with, or None while it is still going
def dead_of(st: S.St) -> Maybe<&2, S.ParseErr>:
  match st:
    case S.St{S.Dead{err}, _a, _g, _s, _p, _b, _o, _r, _n}:
      Some{err}
    case S.St{_mode, _a, _g, _s, _p, _b, _o, _r, _n}:
      None{}

# LAW: a word that starts `--` is flag-shaped
law looks_flag_long:
  for ss: String
  {S.looks_flag("--" ++ ss) == True{} : Bool}

# LAW: empty choices accept every value
law allowed_any:
  for vv: String
  {S.allowed([], vv) == True{} : Bool}

# LAW: `get` on a Matched with no bindings is None
law get_nil:
  for name: String
  {S.get(S.Matched{[], []}, name) == None{} : Maybe<&2, String>}

# LAW: no flag is on in a Matched with no bindings
law on_nil:
  for name: String
  {S.on(S.Matched{[], []}, name) == False{} : Bool}

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
  for dflt: Maybe<&2, String>
  {S.get.last(List.append(&2, String, xs, [vv]), dflt) == Some{vv} : Maybe<&2, String>}

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
law get_last:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  for +vv: String
  for after: {Shake.get_all(S.Matched{path, cs}, name) == [] : List<&2, String>}
  {Shake.get(S.Matched{path, List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs)}, name)
    == Some{vv} : Maybe<&2, String>}

# LAW: `get` is None when nothing binds the name
# SHAKE-GET-1
law get_none:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +name: String
  for none: {Shake.get_all(S.Matched{path, bs}, name) == [] : List<&2, String>}
  {Shake.get(S.Matched{path, bs}, name) == None{} : Maybe<&2, String>}

# LAW: a flag is on exactly when `get` reads Some "true"
# SHAKE-GET-1
law on_some:
  for +found: Shake.Matched
  for +name: String
  for +vv: String
  for h_get: {Shake.get(found, name) == Some{vv} : Maybe<&2, String>}
  {Shake.on(found, name) == String.eq(vv, "true") : Bool}

# LAW: nothing is on that nothing bound
# SHAKE-GET-1
law on_none:
  for +found: Shake.Matched
  for +name: String
  for h_get: {Shake.get(found, name) == None{} : Maybe<&2, String>}
  {Shake.on(found, name) == False{} : Bool}

# LAW: `path_of` is the selected path
# SHAKE-GET-1
law path_of_path:
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  {Shake.path_of(S.Matched{path, bs}) == path : List<&2, String>}

# LAW: `copy` keeps every word IO.args gives, all of them, in order and
# unchanged: read back, the copy is the list it was made from
# SHAKE-ARGS-1
law copy_keeps:
  for xs: List<&1, String>
  {down(Args.copy(xs)) == xs : List<&1, String>}

# LAW: walking two word lists is walking the first, then the second (a lemma)
law walk_append:
  for xs: List<&2, String>
  for ys: List<&2, String>
  for st: S.St
  {S.parse.walk(List.append(&2, String, xs, ys), st)
    == S.parse.walk(ys, S.parse.walk(xs, st)) : S.St}

# LAW: a failed walker stays as it is, whatever words follow (a lemma)
law dead_walk:
  for ys: List<&2, String>
  for +err: S.ParseErr
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  {S.parse.walk(ys, S.St{S.Dead{err}, args, specs, subs, path, binds, pos, raw, seen})
    == S.St{S.Dead{err}, args, specs, subs, path, binds, pos, raw, seen} : S.St}

# LAW: a walker that has failed finishes as that failure, whatever words
# follow (a lemma)
law fail_from:
  for st: S.St
  for +more: List<&2, String>
  for +err: S.ParseErr
  for died: {dead_of(st) == Some{err} : Maybe<&2, S.ParseErr>}
  {S.parse.finish(S.parse.walk(more, st)) == Fail{err}
    : Result<&2, &2, S.ParseErr, S.Matched>}

# LAW: once a word makes the parse fail, the words after it do not change the
# error
# SHAKE-PARSE-9
law fail_stays:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +more: List<&2, String>
  for +err: Shake.ParseErr
  for died: {dead_of(S.parse.walk(ws, S.parse.start(spec))) == Some{err} : Maybe<&2, S.ParseErr>}
  {Shake.parse(spec, List.append(&2, String, ws, more)) == Fail{err}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: every string starts with the empty string (a lemma)
law prefix_empty:
  for ss: String
  {String.starts_with(ss, "") == True{} : Bool}

# LAW: dropping nothing from a string leaves it (a lemma)
law drop_zero:
  for ss: String
  {String.drop(ss, 0n) == ss : String}

# LAW: in a free walker, a long option whose spelling no argument of the
# current command has kills the walk with UnknownFlag of the whole word (a
# step lemma)
law unknown_long_step:
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  {S.parse.step("--" ++ body, S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}

# LAW: a walk that reaches an unknown long option dies there (a lemma)
law unknown_long_dies:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  {dead_of(S.parse.walk(List.append(&2, String, pre, ["--" ++ body]), S.parse.start(spec)))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}

# LAW: wherever the words before it leave the parse, in any command and with
# any bindings, a long option that no argument of that command spells fails
# the parse with UnknownFlag of the word, whatever follows
# SHAKE-TOK-7
law unknown_long:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.UnknownFlag{path, "--" ++ body}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: when the words before `tok` reach a state where `tok` fails the walk,
# the walk through `tok` has failed with that error (a lemma)
law step_dies:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +tok: String
  for +st: S.St
  for +err: S.ParseErr
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}
  {dead_of(S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)))
    == Some{err} : Maybe<&2, S.ParseErr>}

# LAW: when the words before `tok` reach a state where `tok` fails the walk,
# the parse fails with that error, whatever follows (a lemma: every refusal
# row is its step fact through this)
law refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +st: S.St
  for +err: S.ParseErr
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {dead_of(S.parse.step(tok, st)) == Some{err} : Maybe<&2, S.ParseErr>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{err} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: once a short cluster has ended, the letters left change nothing (a
# lemma)
law cluster_done:
  for body: String
  for +orig: String
  for +st: S.St
  {S.cluster(body, orig, st, True{}) == st : S.St}

# LAW: in a free walker, a short option word whose first letter no argument
# of the current command has kills the walk with UnknownFlag of the whole
# word (a step lemma)
law unknown_short_step:
  for +cc: Char
  for +rest: String
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  {S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}

# LAW: wherever the words before it leave the walker free, a short option
# word whose first letter no argument of that command has fails the parse
# with UnknownFlag of the word, whatever follows
# SHAKE-TOK-7
law unknown_short:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +cc: Char
  for +rest: String
  for +args: List<&2, S.Arg>
  for +specs: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, specs, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["-" ++ SCon{cc, rest}]), more))
    == Fail{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

