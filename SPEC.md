# shake specification

This is the list of every behavior shake guarantees, each under a stable requirement ID. Every requirement is about the interface in `main.bend`: its types, builders, `parse`, `check`, the readers, `help`, `err_text`, `help_path`, `err_path` and `argv`. Every module under `src/` is internal and carries no promise.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `src/LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption shake cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend src/PROOF.bend` prints is exactly `All terms check.` (`ez prove`). Tests and fixtures are never evidence for a requirement.

A spec is **well-formed** when `check` reports nothing for it (SHAKE-SPEC-1). The parse requirements hold for well-formed specs; a spec that contradicts itself, such as two options spelled `-n`, is its author's bug and not an input a user can give. Every error a row names but `NeedHelp` also carries `at`, the command path selected where the parse failed (SHAKE-ERR-2); rows write it only where it matters. A **plain word** is `-`, or a word that does not start with `-`. The **current command** is the command whose arguments `parse` matches words against: the root, then each subcommand it selects. The **selected path** is the names of the subcommands selected, in order. A successful parse answers the root command's **Matched**, as clap answers `ArgMatches`: the bindings that command made while it was current and, when a subcommand was selected under it, that subcommand's name and its own Matched, and so on down the selected path.

The words `parse` receives are what the program passes it. In a compiled program they come from `argv`, after the runtime has taken its own flags and the first `--` (SHAKE-TRUST-2).

The reasoning behind each requirement, the verdict of each against the code at `b93357a`, and the decisions that shaped them are in [docs/rfc/shake-spec.md](docs/rfc/shake-spec.md). Every law as it stood then, and the progress of the rollout, is in [docs/rfc/shake-law-inventory.md](docs/rfc/shake-law-inventory.md).

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and "Left to prove" says what is missing.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a request for help has no error text
# SHAKE-ERR-1
law err_text_help:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

### How a word is read (SHAKE-TOK)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-TOK-1 | A word that starts with `--`, is not exactly `--`, and has at least one char before its first `=` is a long option: the chars between `--` and the first `=` (or the end) are its spelling, and when there is an `=` everything after it, verbatim and possibly empty, is its value. A word `--=...` is refused as `UnknownFlag{word}`. | Proved | proved | src/LAWS.bend long_no_name; src/LAWS.bend long_binds; src/LAWS.bend cut_first_eq; src/LAWS.bend cut_no_eq |
| SHAKE-TOK-2 | A word that starts with `-`, is not `-` and does not start with `--` is a cluster of short options, read letter by letter: a letter that spells a flag binds it and the next letter goes on; a letter that spells an option takes the rest of the word as its value, after one `=` when the rest starts with it (verbatim, and possibly empty), or the next word when nothing is left; a letter no argument of the current command spells refuses the whole word as `UnknownFlag{word}`. | Proved | proved | src/LAWS.bend short_step; src/LAWS.bend letter_flag; src/LAWS.bend letter_value; src/LAWS.bend letter_value_eq; src/LAWS.bend letter_value_next; src/LAWS.bend letter_unknown |
| SHAKE-TOK-3 | A plain word is never read as an option. | Proved | proved | src/LAWS.bend plain_word_step; src/LAWS.bend dash_word_step; src/LAWS.bend value_binds; src/LAWS.bend value_refused; src/LAWS.bend raw_next; src/LAWS.bend help_walk |
| SHAKE-TOK-4 | When a word exactly `--` reaches `parse` where an option could stand, it binds nothing and every later word is read as a plain word bound to a positional, whatever its shape. | Proved | proved | src/LAWS.bend dd_step; src/LAWS.bend raw_next; src/LAWS.bend raw_binds; src/LAWS.bend raw_no_pos; src/LAWS.bend raw_refused |
| SHAKE-TOK-5 | A flag given a value (`--verbose=x`, or `-v=x` in a cluster) is refused as `Unexpected{word}`. | Proved | proved | src/LAWS.bend flag_long_valued; src/LAWS.bend letter_flag_eq |
| SHAKE-TOK-6 | An option given no value in its own word takes the next word as its value, unless that word starts with `-` and is not `-`, or there is none; then the parse fails with `NoValue{name}`. | Proved | proved | src/LAWS.bend value_flag_shaped; src/LAWS.bend value_absent; src/LAWS.bend value_binds |
| SHAKE-TOK-7 | A long or short spelling that no argument of the current command has is refused as `UnknownFlag{word}`. Arguments of a parent command are not matched after a subcommand is selected. | Proved | proved | src/LAWS.bend unknown_long; src/LAWS.bend unknown_short; src/LAWS.bend enter_step; src/LAWS.bend letter_unknown |

### What a parse binds (SHAKE-PARSE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-PARSE-1 | For every well-formed spec and word list, when `parse` succeeds, every binding in the Matched of each command on the selected path is either a value-carrying piece of the words given while that command was current (a plain word bound to a positional, the value part of an option word, or the word after an option), bound verbatim under the name of the argument it was given for, or the default of an argument of that command that the words did not bind. The number of bindings that are not defaults equals the number of value-carrying pieces. | Proved | pending |  |
| SHAKE-PARSE-2 | Plain words that select no subcommand bind the current command's positionals in spec order, one word each; a plain word with no positional left is refused as `Unexpected{word}`. | Proved | proved | src/LAWS.bend no_pos_left; src/LAWS.bend pos_next; src/LAWS.bend pos_binds; src/LAWS.bend start_state; src/LAWS.bend enter_step; src/LAWS.bend pos_of_app; src/LAWS.bend pos_of_pos; src/LAWS.bend pos_of_opt; src/LAWS.bend help_word_next; src/LAWS.bend help_word_binds |
| SHAKE-PARSE-3 | A rest positional binds every remaining plain word that selects no subcommand, in order, each under the rest's name. | Proved | proved | src/LAWS.bend rest_next; src/LAWS.bend rest_binds; src/LAWS.bend rest_raw_next; src/LAWS.bend rest_raw_binds |
| SHAKE-PARSE-4 | Before `--`, a plain word that names a subcommand of the current command selects it: the selected path gains that name, its arguments become current, and the bindings made so far stay with the command that made them; the subcommand's own bindings start empty. When a pending positional of the current command is required, has no default and is not a rest, the parse fails instead with `Missing{name}` of the first such one; a rest positional does not block a subcommand, and SHAKE-PARSE-7 checks it when the words end. | Proved | proved | src/LAWS.bend enter_step; src/LAWS.bend enter_missing; src/LAWS.bend none_blocking; src/LAWS.bend first_blocking |
| SHAKE-PARSE-5 | A value given to an argument with a nonempty choices list binds only when it is in the list, and otherwise fails with `BadValue{name, value}`. An argument with no choices accepts every value. | Proved | proved | src/LAWS.bend choice_refused; src/LAWS.bend value_refused; src/LAWS.bend long_refused; src/LAWS.bend raw_refused; src/LAWS.bend letter_value_bad; src/LAWS.bend pos_next; src/LAWS.bend pos_binds; src/LAWS.bend raw_binds; src/LAWS.bend value_binds; src/LAWS.bend long_binds; src/LAWS.bend letter_value; src/LAWS.bend letter_value_eq |
| SHAKE-PARSE-6 | After the last word, each argument of every command on the selected path that the words left unbound in that command and that has a default is bound to its default in that command's Matched. A bound argument's value is never replaced, and no argument without a default gains a binding. | Proved | proved | src/LAWS.bend default_filled; src/LAWS.bend bound_kept; src/LAWS.bend no_default; src/LAWS.bend no_argument |
| SHAKE-PARSE-7 | A successful parse binds every required argument of every command on the selected path, in that command's Matched. Otherwise the parse fails with `Missing{name}`. | Proved | proved | src/LAWS.bend required_present; src/LAWS.bend required_missing |
| SHAKE-PARSE-8 | Before `--` and before any positional of the current command is bound, a plain word `help` makes the parse fail with `NeedHelp{path}`, where `path` is the selected path followed by the remaining words, as long as each names a subcommand under the one before; the first remaining word that does not makes the parse fail with `Unexpected{word}`. | Proved | proved | src/LAWS.bend help_unknown; src/LAWS.bend help_step; src/LAWS.bend help_walk; src/LAWS.bend help_path |
| SHAKE-PARSE-9 | Once a word makes the parse fail, the words after it do not change the error. | Proved | proved | src/LAWS.bend fail_stays |
| SHAKE-PARSE-10 | A flag or an option built with `opt` that is given a second time while the same command is current, under any of its spellings, fails the parse with `Repeated{at, name}`; an argument of a parent command with the same name is a different argument (SHAKE-TOK-7). An option built with `many` binds every value given, in the order given, and `get_all` of its command's Matched reads them all. | Proved | proved | src/LAWS.bend repeated_long_flag; src/LAWS.bend repeated_long_opt; src/LAWS.bend letter_flag_again; src/LAWS.bend letter_opt_again; src/LAWS.bend long_binds; src/LAWS.bend letter_value; src/LAWS.bend letter_value_eq |

### Checking a spec (SHAKE-SPEC)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-SPEC-1 | `check(spec)` reports exactly one error for each of: a rest positional that is not its command's last positional; an argument of a command with the name, short spelling or long spelling of an earlier argument of that command; a subcommand with the name of an earlier subcommand of the same command; a subcommand named `help`; a default outside its argument's nonempty choices; a required positional after an optional one. It reports nothing else. | Proved | pending |  |

### Reading a result (SHAKE-GET)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-GET-1 | For every Matched `m` and name: `get(m, name)` is `Some` of the value of the last binding of that name that `m`'s command made, or `None` when it made none; `get_all(m, name)` is the values of every binding of that name that `m`'s command made, in binding order; `on(m, name)` is true exactly when `get(m, name)` is `Some{"true"}`. A command's Matched reads only its own bindings: the subcommand selected under it changes none of these. | Proved | proved | src/LAWS.bend get_all_append; src/LAWS.bend get_all_hit; src/LAWS.bend get_all_miss; src/LAWS.bend get_last; src/LAWS.bend get_none; src/LAWS.bend on_some; src/LAWS.bend on_none; src/LAWS.bend get_all_node; src/LAWS.bend get_node |
| SHAKE-GET-2 | For every Matched `m`: `sub_name(m)` is `Some` of the name of the subcommand selected under `m`'s command, or `None` when none was; `sub_of(m, name)` is that subcommand's Matched when its name is `name`, and `None` otherwise; `path_of(m)` is the names of the subcommands selected below `m`'s command, in order, so the whole selected path for the Matched `parse` answers; `at(m, [])` is `Some{m}`, and `at(m, name <> rest)` is `at` of `sub_of(m, name)` and `rest`, or `None` when `sub_of` is `None`. | Proved | proved | src/LAWS.bend sub_name_leaf; src/LAWS.bend sub_name_node; src/LAWS.bend sub_of_hit; src/LAWS.bend sub_of_miss; src/LAWS.bend sub_of_leaf; src/LAWS.bend path_of_leaf; src/LAWS.bend path_of_node; src/LAWS.bend at_nil; src/LAWS.bend at_cons |

### Help pages (SHAKE-HELP)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-HELP-1 | `help(spec, path)` renders the page of the command reached by following each name of `path` from the root through the subcommands, skipping a name that is not a subcommand where it stands. | Proved | proved | src/LAWS.bend help_page; src/LAWS.bend reach_child; src/LAWS.bend reach_skip |
| SHAKE-HELP-2 | A page lists each subcommand of its command exactly once, in spec order, followed by `help`, and each flag and option exactly once, in spec order. Its usage line names each positional exactly once, in spec order, as `<NAME>` when required and `[NAME]` otherwise, with `...` after a rest positional. | Proved | pending |  |

### Errors (SHAKE-ERR)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-ERR-1 | `err_text(spec, err)` is empty exactly when `help_path(err)` is `Some`, that is, when the parse failed with a request for help. | Proved | proved | src/LAWS.bend err_text_help; src/LAWS.bend err_text_iff |
| SHAKE-ERR-2 | For every error but a request for help, `err_path(err)` is the path of subcommands the parse had selected at the word that failed it, and `err_text(spec, err)` shows the usage line of the command at that path, as `help(spec, err_path(err))` does. | Proved | proved | src/LAWS.bend err_path_at; src/LAWS.bend err_text_usage; src/LAWS.bend help_page; src/LAWS.bend unknown_long; src/LAWS.bend unknown_short; src/LAWS.bend no_pos_left; src/LAWS.bend choice_refused; src/LAWS.bend flag_long_valued; src/LAWS.bend value_flag_shaped; src/LAWS.bend value_absent; src/LAWS.bend help_unknown; src/LAWS.bend long_no_name; src/LAWS.bend repeated_long_flag; src/LAWS.bend repeated_long_opt; src/LAWS.bend value_refused; src/LAWS.bend long_refused; src/LAWS.bend raw_no_pos; src/LAWS.bend raw_refused; src/LAWS.bend enter_missing; src/LAWS.bend required_missing; src/LAWS.bend letter_flag_eq; src/LAWS.bend letter_unknown; src/LAWS.bend letter_flag_again; src/LAWS.bend letter_opt_again; src/LAWS.bend letter_value_bad |

### The argument list (SHAKE-ARGS)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-ARGS-1 | The copy `argv` makes of the words `IO.args` gives keeps all of them, in order and unchanged: for every list, reading the copy back gives the list. | Proved | proved | src/LAWS.bend copy_keeps |

## Left to prove

Every pending row is unproved in full: no pending row has partial laws. The RFC's Rollout and [docs/rfc/shake-walker-proofs.md](docs/rfc/shake-walker-proofs.md) say in which phase each row's laws land. Every walker law holds wherever the words before the word it is about leave the walker in the state its premise names.

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| SHAKE-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law. | It cannot be checked from inside Bend; this is EZ-TRUST-1. shake pins bend 2.0.27 through the flake. |
| SHAKE-TRUST-2 | A program compiled by bend 2.0.27 hands `IO.args` the process's words after the program name, except that it stops examining words at the first `--`, drops that `--` and passes every later word through unchanged; before that `--` it removes `--threads` and `--gpu` with the word after each, and ends the process before `main` on `--help` and on `--gpu-build`. | It is the C `main` bend emits, read from bend 2.0.26's own source (in its binary) and confirmed against the demo; rechecked for 2.0.27, whose `main` is identical. It changes when bend does, so every bend bump rechecks it. |
| SHAKE-TRUST-3 | The proof-gate runner fails the build unless the first line of `bend src/PROOF.bend` is `All terms check.` | It is ez's `mkProofs` running `ez prove`, run by `nix flake check` in CI; this is EZ-TRUST-4. |
| SHAKE-TRUST-4 | `argv` hands on exactly the list `IO.args` answers, through the copy SHAKE-ARGS-1 is about. | It is IO, which no law can reach: `argv` in `src/args.bend` is one `IO.bind` of `IO.args` into `copy`, short enough to check by reading, and marked `# noqa: L001` for that reason. |
