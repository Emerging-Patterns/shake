# shake: the laws. The human states them; PROOF.bend must prove them. A law
# tagged with a SPEC.md ID proves that requirement, and its statement changes
# only when the row does. The untagged ones are lemmas for the proofs to come.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/args.bend as Args
import ../src/grow.bend as Grow
import ../src/walk.bend as Walk

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
  {S.get(S.Leaf{[]}, name) == None{} : Maybe<&2, String>}

# LAW: no flag is on in a Matched with no bindings
law on_nil:
  for name: String
  {S.on(S.Leaf{[]}, name) == False{} : Bool}

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
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  {Shake.get_all(S.Leaf{List.append(&2, S.Bind, bs, cs)}, name)
    == List.append(&2, String, Shake.get_all(S.Leaf{bs}, name),
      Shake.get_all(S.Leaf{cs}, name)) : List<&2, String>}

# LAW: one binding of a name gives `get_all` its value
# SHAKE-GET-1
law get_all_hit:
  for +name: String
  for +vv: String
  {Shake.get_all(S.Leaf{[S.Bind{name, vv}]}, name) == [vv] : List<&2, String>}

# LAW: one binding of another name gives `get_all` nothing
# SHAKE-GET-1
law get_all_miss:
  for +other: String
  for +name: String
  for +vv: String
  for differ: {String.eq(other, name) == False{} : Bool}
  {Shake.get_all(S.Leaf{[S.Bind{other, vv}]}, name) == [] : List<&2, String>}

# LAW: `get` is the value of the last binding of the name
# SHAKE-GET-1
law get_last:
  for +bs: List<&2, S.Bind>
  for +cs: List<&2, S.Bind>
  for +name: String
  for +vv: String
  for after: {Shake.get_all(S.Leaf{cs}, name) == [] : List<&2, String>}
  {Shake.get(S.Leaf{List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs)}, name)
    == Some{vv} : Maybe<&2, String>}

# LAW: `get` is None when nothing binds the name
# SHAKE-GET-1
law get_none:
  for +bs: List<&2, S.Bind>
  for +name: String
  for none: {Shake.get_all(S.Leaf{bs}, name) == [] : List<&2, String>}
  {Shake.get(S.Leaf{bs}, name) == None{} : Maybe<&2, String>}

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

# LAW: a command's `get_all` reads only its own bindings: the subcommand
# selected under it changes nothing
# SHAKE-GET-1
law get_all_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  {Shake.get_all(S.Node{bs, nn, below}, name) == Shake.get_all(S.Leaf{bs}, name) : List<&2, String>}

# LAW: a command's `get` reads only its own bindings
# SHAKE-GET-1
law get_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  {Shake.get(S.Node{bs, nn, below}, name) == Shake.get(S.Leaf{bs}, name) : Maybe<&2, String>}

# LAW: no subcommand was selected under a command with no Matched below it
# SHAKE-GET-2
law sub_name_leaf:
  for +bs: List<&2, S.Bind>
  {Shake.sub_name(S.Leaf{bs}) == None{} : Maybe<&2, String>}

# LAW: `sub_name` is the name of the subcommand selected
# SHAKE-GET-2
law sub_name_node:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  {Shake.sub_name(S.Node{bs, nn, below}) == Some{nn} : Maybe<&2, String>}

# LAW: `sub_of` the subcommand selected is its Matched
# SHAKE-GET-2
law sub_of_hit:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  {Shake.sub_of(S.Node{bs, nn, below}, nn) == Some{below} : Maybe<&2, Shake.Matched>}

# LAW: `sub_of` any other name is None
# SHAKE-GET-2
law sub_of_miss:
  for +bs: List<&2, S.Bind>
  for +nn: String
  for +below: Shake.Matched
  for +name: String
  for differ: {String.eq(nn, name) == False{} : Bool}
  {Shake.sub_of(S.Node{bs, nn, below}, name) == None{} : Maybe<&2, Shake.Matched>}

# LAW: `sub_of` is None when no subcommand was selected
# SHAKE-GET-2
law sub_of_leaf:
  for +bs: List<&2, S.Bind>
  for +name: String
  {Shake.sub_of(S.Leaf{bs}, name) == None{} : Maybe<&2, Shake.Matched>}

# LAW: no names are selected below a command with no subcommand selected
# SHAKE-GET-2
law path_of_leaf:
  for +bs: List<&2, S.Bind>
  {Shake.path_of(S.Leaf{bs}) == [] : List<&2, String>}

# LAW: the names selected below a command are its subcommand's name, then the
# names selected below that
# SHAKE-GET-2
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
# SHAKE-GET-2
law at_nil:
  for +found: Shake.Matched
  {Shake.at(found, []) == Some{found} : Maybe<&2, Shake.Matched>}

# LAW: `at` a path follows its first name with `sub_of`, then the rest
# SHAKE-GET-2
law at_cons:
  for +found: Shake.Matched
  for +name: String
  for +rest: List<&2, String>
  {Shake.at(found, name <> rest) == at.via(Shake.sub_of(found, name), rest) : Maybe<&2, Shake.Matched>}

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
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  {S.parse.walk(ys, S.St{S.Dead{err}, args, up, subs, path, binds, pos, raw, seen})
    == S.St{S.Dead{err}, args, up, subs, path, binds, pos, raw, seen} : S.St}

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
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_none: {S.by_long(args, name) == None{} : Maybe<&2, S.Arg>}
  {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}

# LAW: a walk that reaches an unknown long option dies there (a lemma)
law unknown_long_dies:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
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
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
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
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  {S.parse.step("-" ++ SCon{cc, rest}, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.St{S.Dead{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}

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
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("-" ++ SCon{cc, rest}, "--") == False{} : Bool}
  for h_dash: {Char.is_eq(cc, '-') == False{} : Bool}
  for h_none: {S.by_short(args, SCon{cc, SNil{}}) == None{} : Maybe<&2, S.Arg>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["-" ++ SCon{cc, rest}]), more))
    == Fail{S.UnknownFlag{path, "-" ++ SCon{cc, rest}}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}


# LAW: wherever the words before it leave the walker free with no positional
# left, a plain word that names no subcommand fails the parse with Unexpected
# of the word, whatever follows
# SHAKE-PARSE-2
law no_pos_left:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [], False{}, seen} : S.St}
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.Unexpected{path, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free with a positional
# next whose choices do not allow it, a plain word that names no subcommand
# fails the parse with BadValue of that positional and the word, whatever
# follows
# SHAKE-PARSE-5
law choice_refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, seen} : S.St}
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
  for h_bad: {S.allowed(cs, tok) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.BadValue{path, name, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: a free walker hands a long option word to `take_arg`, with the
# argument its name spells and the value after `=` (a step lemma)
law long_arg_step:
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  {S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.take_arg(S.by_long(args, name), val, "--" ++ body, args, up, subs, path, bs, pos,
      False{}, seen) : S.St}

# LAW: wherever the words before it leave the walker free, a long option
# that spells a flag not yet given and gives it a value fails the parse with
# Unexpected of the word, whatever follows
# SHAKE-TOK-5
law flag_long_valued:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +vv: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_once: {S.bound(bs, nn) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.Unexpected{path, "--" ++ body}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave an option waiting for its value, a
# word that starts with `-` and is not `-` fails the parse with Missing of the
# option, whatever follows
# SHAKE-TOK-6
law value_flag_shaped:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_flag: {S.looks_flag(tok) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.NoValue{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: when the words end with an option still waiting for its value, the
# parse fails with Missing of the option
# SHAKE-TOK-6
law value_absent:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(ws, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  {Shake.parse(spec, ws) == Fail{S.NoValue{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}


# LAW: wherever the words before it leave the walker reading a help path, a
# word that names no subcommand where the path stands fails the parse with
# Unexpected of the word, whatever follows
# SHAKE-PARSE-8
law help_unknown:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.Unexpected{path, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free, a word `--=...`,
# with nothing between `--` and `=`, fails the parse with UnknownFlag of the
# word, whatever follows
# SHAKE-TOK-1
law long_no_name:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_empty: {String.is_empty(name) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.UnknownFlag{path, "--" ++ body}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: the once-check, told the name was given before, fails with Repeated
# whatever the step it guards would have done (a lemma)
law once_dead:
  for st: S.St
  for +nn: String
  for +path: List<&2, String>
  {dead_of(S.parse.once(True{}, st, nn, path)) == Some{S.Repeated{path, nn}} : Maybe<&2, S.ParseErr>}

# LAW: wherever the words before it leave the walker free, a long option that
# spells a flag already given fails the parse with Repeated of its name,
# whatever follows
# SHAKE-PARSE-10
law repeated_long_flag:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Flag{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_again: {S.bound(bs, nn) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.Repeated{path, nn}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free, a long option that
# spells an option built with `opt` already given fails the parse with Repeated of its name,
# whatever follows
# SHAKE-PARSE-10
law repeated_long_opt:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +val: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, S.Opt{}, hp, req, dflt, cs}}
    : Maybe<&2, S.Arg>}
  for h_again: {S.bound(bs, nn) == True{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.Repeated{path, nn}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

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

# LAW: when the words `mid`, read where the words before them leave the
# walker, stay in the command at `path` and put bindings `xs` in front of the
# bindings `bs` it made, and the parse succeeds, `get_all` of a name in that
# command's Matched reads its values in `bs`, then its values in `xs`, both in
# the order given, then any it bound after, whatever follows (a lemma)
law kept_all:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +mid: List<&2, String>
  for +more: List<&2, String>
  for +st: S.St
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +xs: List<&2, S.Bind>
  for +bs: List<&2, S.Bind>
  for +name: String
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_mid: {Grow.view(S.parse.walk(mid, st)) == Grow.View{args, up, path, List.append(&2, S.Bind, xs, bs)}
    : Grow.View}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, mid), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name),
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, xs), name), after))}
    : Maybe<&2, List<&2, String>>}

# LAW: when the words before `tok` reach a state where `tok` stays in the
# command at `path` and puts `Bind{name, vv}` in front of the bindings `bs` it
# made, and the parse succeeds, `get_all` of the name in that command's Matched
# reads the values bound to it before `tok`, then `vv`, then any bound after,
# whatever follows (a lemma: every binding row is its step fact through this,
# as every refusal row is through `refused`)
law kept:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +st: S.St
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +name: String
  for +vv: String
  for +bs: List<&2, S.Bind>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
  for h_step: {Grow.view(S.parse.step(tok, st)) == Grow.View{args, up, path, S.Bind{name, vv} <> bs} : Grow.View}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), vv <> after)}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before it leave an option waiting for its value, a
# word that is not flag-shaped and that the option's choices allow is its
# value: when the parse succeeds, `get_all` of the option reads the values
# given it before, then the word, whatever follows
# SHAKE-TOK-6
# SHAKE-PARSE-5
law value_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_flag: {S.looks_flag(tok) == False{} : Bool}
  for h_ok: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), tok <> after)}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before it leave the walker free with a positional
# next, a plain word that names no subcommand and that the positional's
# choices allow binds to it, and the walker goes on free with the positionals
# after it pending (a rest positional stays pending)
# SHAKE-PARSE-2
# SHAKE-PARSE-5
law pos_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, seen} : S.St}
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
  for h_ok: {S.allowed(cs, tok) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}

# LAW: wherever the words before it leave the walker free with a positional
# next, a plain word that names no subcommand and that the positional's
# choices allow is its value: when the parse succeeds, `get_all` of the
# positional reads the values bound to it before, then the word, whatever
# follows
# SHAKE-PARSE-2
# SHAKE-PARSE-5
law pos_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, seen} : S.St}
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>}
  for h_ok: {S.allowed(cs, tok) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), tok <> after)}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before it leave the walker free and before `--`, a
# word `--` binds nothing and leaves it free after `--`
# SHAKE-TOK-4
law dd_step:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  {S.parse.walk(List.append(&2, String, pre, ["--"]), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, True{}, seen} : S.St}

# LAW: wherever the words before it leave the walker free after `--`, any
# word, whatever its shape, is read as a plain word bound to the next
# positional: one its choices allow binds, and the walker goes on free after
# `--` with the positionals after it pending
# SHAKE-TOK-4
law raw_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      True{}, seen} : S.St}
  for h_ok: {S.allowed(cs, tok) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), True{}, True{}} : S.St}

# LAW: wherever the words before it leave the walker free after `--` with a
# positional next, any word its choices allow, whatever its shape, is its
# value: when the parse succeeds, `get_all` of the positional reads the values
# bound to it before, then the word, whatever follows
# SHAKE-TOK-4
# SHAKE-PARSE-5
law raw_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      True{}, seen} : S.St}
  for h_ok: {S.allowed(cs, tok) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, name)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), name), tok <> after)}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before it leave the walker free after `--` with no
# positional left, any word fails the parse with Unexpected of the word,
# whatever follows
# SHAKE-TOK-4
law raw_no_pos:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [], True{}, seen} : S.St}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.Unexpected{path, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free after `--` with a
# positional next whose choices do not allow it, any word fails the parse
# with BadValue, whatever follows
# SHAKE-TOK-4
# SHAKE-PARSE-5
law raw_refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +name: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +rest: List<&2, S.Arg>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      True{}, seen} : S.St}
  for h_bad: {S.allowed(cs, tok) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.BadValue{path, name, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# whether an option of this kind binds a value given it now: one built with
# `opt` when it was not given before, one built with `many` always
def takes(kk: S.ArgKind, given: Bool) -> Bool:
  match kk:
    case S.Opt{}:
      Bool.not(given)
    case S.Many{}:
      True{}
    case _other:
      False{}

# LAW: wherever the words before it leave the walker free, a long option
# `--name=vv` that spells an option built with `opt` not yet given, or one
# built with `many`, and whose choices allow `vv`, binds `vv`: when the parse
# succeeds, `get_all` of the option reads the values given it before, then
# `vv`, whatever follows
# SHAKE-TOK-1
# SHAKE-PARSE-5
# SHAKE-PARSE-10
law long_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +vv: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>}
  for h_kind: {takes(kind, S.bound(bs, nn)) == True{} : Bool}
  for h_ok: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, nn)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nn), vv <> after)}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before it leave an option waiting for its value, a
# word that is not flag-shaped and that the option's choices do not allow
# fails the parse with BadValue of the option and the word, whatever follows
# SHAKE-PARSE-5
law value_refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +tok: String
  for +name: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +raw: Bool
  for +seen: Bool
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen} : S.St}
  for h_flag: {S.looks_flag(tok) == False{} : Bool}
  for h_bad: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, [tok]), more))
    == Fail{S.BadValue{path, name, tok}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: wherever the words before it leave the walker free, a long option
# `--name=vv` that spells an option built with `opt` not yet given, or one
# built with `many`, and whose choices do not allow `vv`, fails the parse with
# BadValue of the option and `vv`, whatever follows
# SHAKE-PARSE-5
law long_refused:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +more: List<&2, String>
  for +body: String
  for +name: String
  for +vv: String
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +pos: List<&2, S.Arg>
  for +seen: Bool
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  for h_dd: {String.eq("--" ++ body, "--") == False{} : Bool}
  for h_cut: {S.cut_eq(body) == (name, Some{vv}) : String & Maybe<&2, String>}
  for h_name: {String.is_empty(name) == False{} : Bool}
  for h_found: {S.by_long(args, name) == Some{S.Arg{nn, sh, lo, kind, hp, req, dflt, cs}} : Maybe<&2, S.Arg>}
  for h_kind: {takes(kind, S.bound(bs, nn)) == True{} : Bool}
  for h_bad: {S.allowed(S.parse.choices(S.by_name(args, nn)), vv) == False{} : Bool}
  {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more))
    == Fail{S.BadValue{path, nn, vv}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# whether a string has no `=`
def no_eq(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+cc, tt}:
      Bool.and(Bool.not(Char.is_eq(cc, '=')), no_eq(tt))

# LAW: the `=` cut of a long option's body splits it at its first `=`: the
# chars before it are the spelling, and everything after it, verbatim and
# possibly empty, is the value
# SHAKE-TOK-1
law cut_first_eq:
  for +name: String
  for +vv: String
  for h_name: {no_eq(name) == True{} : Bool}
  {S.cut_eq(name ++ ("=" ++ vv)) == (name, Some{vv}) : String & Maybe<&2, String>}

# LAW: a long option's body with no `=` is all spelling, with no value
# SHAKE-TOK-1
law cut_no_eq:
  for +name: String
  for h_name: {no_eq(name) == True{} : Bool}
  {S.cut_eq(name) == (name, None{}) : String & Maybe<&2, String>}

# whether a choices list allows every word
def all_allowed(+cs: List<&2, String>, ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, tt}:
      Bool.and(S.allowed(cs, ww), all_allowed(cs, tt))

# LAW: wherever the words before them leave the walker free before `--`, with
# only a rest positional left, plain words that name no subcommand and that its
# choices allow each bind it, in order, and the walker stays free with the
# rest still pending
# SHAKE-PARSE-3
law rest_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, seen}
    : S.St}
  for h_plain: {Walk.all_plain(fs) == True{} : Bool}
  for h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs),
      [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, Walk.wk.seen(fs, seen)} : S.St}

# LAW: wherever the words before them leave the walker free before `--`, with
# only a rest positional left, plain words that name no subcommand and that its
# choices allow are its values: when the parse succeeds, `get_all` of the rest
# in its command's Matched reads the values bound to it before, then the words,
# in order, whatever follows
# SHAKE-PARSE-3
law rest_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +more: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], False{}, seen}
    : S.St}
  for h_plain: {Walk.all_plain(fs) == True{} : Bool}
  for h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, fs), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}

# LAW: wherever the words before them leave the walker free after `--`, with
# only a rest positional left, words its choices allow, whatever their shape,
# each bind it, in order, and the walker stays free after `--` with the rest
# still pending
# SHAKE-PARSE-3
law rest_raw_next:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, seen}
    : S.St}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs),
      [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, Walk.wk.seen(fs, seen)} : S.St}

# LAW: wherever the words before them leave the walker free after `--`, with
# only a rest positional left, words its choices allow, whatever their shape,
# are its values: when the parse succeeds, `get_all` of the rest in its
# command's Matched reads the values bound to it before, then the words, in
# order, whatever follows
# SHAKE-PARSE-3
law rest_raw_binds:
  for +spec: Shake.Cli
  for +pre: List<&2, String>
  for +fs: List<&2, String>
  for +more: List<&2, String>
  for +args: List<&2, S.Arg>
  for +up: List<&2, S.Level>
  for +subs: List<&2, S.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +seen: Bool
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +found: Shake.Matched
  for h_at: {S.parse.walk(pre, S.parse.start(spec))
    == S.St{S.Free{}, args, up, subs, path, bs, [S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}], True{}, seen}
    : S.St}
  for h_ok: {all_allowed(cs, fs) == True{} : Bool}
  for h_done: {Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, fs), more)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs after: List<&2, String>
  {all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}

# whether no argument of a list is named `name`
def none_named(args: List<&2, S.Arg>, +name: String) -> Bool:
  match args:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Arg{+nn, _s, _l, _k, _h, _r, _d, _c} = hh
      Bool.and(Bool.not(String.eq(nn, name)), none_named(tt, name))

# whether a name has values in the command at `path` in a Matched, when the
# path reaches one
def present_at.go(mm: Maybe<&2, Shake.Matched>, +name: String) -> Maybe<&2, Bool>:
  match mm:
    case None{}:
      None{}
    case Some{found}:
      Some{Bool.not(List.is_empty(&2, String, Shake.get_all(found, name)))}

# whether a name has values in the command at `path` in a Matched
def present_at(found: Shake.Matched, path: List<&2, String>, +name: String) -> Maybe<&2, Bool>:
  present_at.go(Shake.at(found, path), name)

# whether a mode is free
def free.mode(mode: S.Mode) -> Bool:
  match mode:
    case S.Free{}:
      True{}
    case _other:
      False{}

# whether a walker is free
def free(st: S.St) -> Bool:
  S.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  free.mode(mode)

# LAW: when the parse succeeds, an argument with a default that its command
# left unbound reads its default, once, in that command's Matched
# SHAKE-PARSE-6
law default_filled:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dd: String
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, Some{dd}, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  for h_free: {S.bound(bs, nn) == False{} : Bool}
  {all_at(found, path, nn) == Some{[dd]} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, an argument its command bound reads exactly
# the values it was given, in order, in that command's Matched: a default
# never replaces them nor adds to them
# SHAKE-PARSE-6
law bound_kept:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, dflt, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  for h_bound: {S.bound(bs, nn) == True{} : Bool}
  {all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, an argument with no default reads only the
# values the words gave it in its command's Matched, none when they gave none
# SHAKE-PARSE-6
law no_default:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, req, None{}, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_pa: {none_named(pa, nn) == True{} : Bool}
  for h_qa: {none_named(qa, nn) == True{} : Bool}
  {all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, a name no argument of a command has reads only
# what the words bound to it in that command's Matched
# SHAKE-PARSE-6
law no_argument:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +args: List<&2, S.Arg>
  for +nn: String
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  for h_none: {none_named(args, nn) == True{} : Bool}
  {all_at(found, path, nn) == Some{S.get_all.bind(List.reverse(&2, S.Bind, bs), nn)} : Maybe<&2, List<&2, String>>}

# LAW: when the parse succeeds, every required argument of every command on
# the selected path has a value in that command's Matched
# SHAKE-PARSE-7
law required_present:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +found: Shake.Matched
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for +ms: List<&2, String>
  for h_done: {Shake.parse(spec, ws) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), bs} <> up),
      List.append(&2, String, path, ms)} : Grow.Frame}
  for h_len: {List.length(&2, S.Level, up) == List.length(&2, String, path) : Nat}
  {present_at(found, path, nn) == Some{True{}} : Maybe<&2, Bool>}

# LAW: when the words end with the walker free and a required argument of a
# command on the selected path unbound and without a default, the parse fails
# with Missing at the selected path
# SHAKE-PARSE-7
law required_missing:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +qs: List<&2, S.Level>
  for +pa: List<&2, S.Arg>
  for +qa: List<&2, S.Arg>
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +dflt: Maybe<&2, String>
  for +cs: List<&2, String>
  for +bs: List<&2, S.Bind>
  for +up: List<&2, S.Level>
  for +path: List<&2, String>
  for h_free: {free(S.parse.walk(ws, S.parse.start(spec))) == True{} : Bool}
  for h_fr: {Grow.gw.frame(S.parse.walk(ws, S.parse.start(spec)))
    == Grow.Frame{List.append(&2, S.Level, qs,
      S.Level{List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa), bs} <> up), path}
    : Grow.Frame}
  for h_unbound: {S.bound(S.fill.args(List.append(&2, S.Arg, pa, S.Arg{nn, sh, lo, kind, hp, True{}, dflt, cs} <> qa),
    bs), nn) == False{} : Bool}
  exs name: String
  {Shake.parse(spec, ws) == Fail{S.Missing{path, name}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
