# shake specification

This is the list of every behavior shake guarantees, each under a stable requirement ID. Every requirement is about the interface in `main.bend`: its types, builders, `parse`, `check`, the readers, `help`, `err_text`, `help_path` and `argv`. Every module under `src/` is internal and carries no promise.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `src/LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption shake cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend src/PROOF.bend` prints is exactly `All terms check.` (`ez prove`). Tests and fixtures are never evidence for a requirement.

A spec is **well-formed** when `check` reports nothing for it (SHAKE-SPEC-1). The parse requirements hold for well-formed specs; a spec that contradicts itself, such as two options spelled `-n`, is its author's bug and not an input a user can give. A **plain word** is `-`, or a word that does not start with `-`. The **current command** is the command whose arguments `parse` matches words against: the root, then each subcommand it selects. The **selected path** is the names of the subcommands selected, in order.

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
| SHAKE-TOK-1 | A word that starts with `--`, is not exactly `--`, and has at least one char before its first `=` is a long option: the chars between `--` and the first `=` (or the end) are its spelling, and when there is an `=` everything after it, verbatim and possibly empty, is its value. A word `--=...` is refused as `UnknownFlag{word}`. | Proved | pending |  |
| SHAKE-TOK-2 | A word that starts with `-`, is not `-` and does not start with `--` is a short option: its second char is the spelling, and the rest of the word, verbatim and including any `=`, is its value when it is not empty. | Proved | pending |  |
| SHAKE-TOK-3 | A plain word is never read as an option. | Proved | pending |  |
| SHAKE-TOK-4 | When a word exactly `--` reaches `parse` where an option could stand, it binds nothing and every later word is read as a plain word bound to a positional, whatever its shape. | Proved | pending |  |
| SHAKE-TOK-5 | A flag given a value (`--verbose=x`, `-vx`) is refused as `Unexpected{word}`. | Proved | pending |  |
| SHAKE-TOK-6 | An option given no value in its own word takes the next word as its value, unless that word starts with `-` and is not `-`, or there is none; then the parse fails with `Missing{name}`. | Proved | pending |  |
| SHAKE-TOK-7 | A long or short spelling that no argument of the current command has is refused as `UnknownFlag{word}`. Arguments of a parent command are not matched after a subcommand is selected. | Proved | pending |  |

### What a parse binds (SHAKE-PARSE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-PARSE-1 | For every well-formed spec and word list, when `parse` succeeds, every binding is either a value-carrying piece of the words (a plain word bound to a positional, the value part of an option word, or the word after an option), bound verbatim under the name of the argument it was given for, or the default of an argument on the selected path that the words did not bind. The number of bindings that are not defaults equals the number of value-carrying pieces. | Proved | pending |  |
| SHAKE-PARSE-2 | Plain words that select no subcommand bind the current command's positionals in spec order, one word each; a plain word with no positional left is refused as `Unexpected{word}`. | Proved | pending |  |
| SHAKE-PARSE-3 | A rest positional binds every remaining plain word that selects no subcommand, in order, each under the rest's name. | Proved | pending |  |
| SHAKE-PARSE-4 | Before `--`, a plain word that names a subcommand of the current command selects it: the selected path gains that name, its arguments become current, and bindings made so far are kept. When a required positional of the current command is still unbound, the parse fails with `Missing{name}` of the first such one instead. | Proved | pending |  |
| SHAKE-PARSE-5 | A value given to an argument with a nonempty choices list binds only when it is in the list, and otherwise fails with `BadValue{name, value}`. An argument with no choices accepts every value. | Proved | pending |  |
| SHAKE-PARSE-6 | After the last word, each argument of every command on the selected path that the words left unbound and that has a default is bound to its default. A bound argument's value is never replaced, and no argument without a default gains a binding. | Proved | pending |  |
| SHAKE-PARSE-7 | A successful parse binds every required argument of every command on the selected path. Otherwise the parse fails with `Missing{name}`. | Proved | pending |  |
| SHAKE-PARSE-8 | Before `--` and before any positional of the current command is bound, a plain word `help` makes the parse fail with `NeedHelp{path}`, where `path` is the selected path followed by the remaining words, as long as each names a subcommand under the one before; the first remaining word that does not makes the parse fail with `Unexpected{word}`. | Proved | pending |  |
| SHAKE-PARSE-9 | Once a word makes the parse fail, the words after it do not change the error. | Proved | proved | src/LAWS.bend fail_stays |
| SHAKE-PARSE-10 | When an option or flag is given more than once, `get` reads the last value given and `get_all` every value, in the order given. | Proved | pending |  |

### Checking a spec (SHAKE-SPEC)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-SPEC-1 | `check(spec)` reports exactly one error for each of: a rest positional that is not its command's last positional; an argument of a command with the name, short spelling or long spelling of an earlier argument of that command; a subcommand with the name of an earlier subcommand of the same command; a subcommand named `help`; a default outside its argument's nonempty choices; a required positional after an optional one. It reports nothing else. | Proved | pending |  |

### Reading a result (SHAKE-GET)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-GET-1 | For every Matched and name: `get` is the value of the last binding with that name, or `""` when there is none; `get_all` is the values of every binding with that name, in binding order; `on` is true exactly when `get` is `"true"`; `path_of` is the selected path. | Proved | proved | src/LAWS.bend get_all_append; src/LAWS.bend get_all_hit; src/LAWS.bend get_all_miss; src/LAWS.bend get_last; src/LAWS.bend get_none; src/LAWS.bend on_get; src/LAWS.bend path_of_path |

### Help pages (SHAKE-HELP)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-HELP-1 | `help(spec, path)` renders the page of the command reached by following each name of `path` from the root through the subcommands, skipping a name that is not a subcommand where it stands. | Proved | pending |  |
| SHAKE-HELP-2 | A page lists each subcommand of its command exactly once, in spec order, followed by `help`, and each flag and option exactly once, in spec order. Its usage line names each positional exactly once, in spec order, as `<NAME>` when required and `[NAME]` otherwise, with `...` after a rest positional. | Proved | pending |  |

### Errors (SHAKE-ERR)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-ERR-1 | `err_text(spec, err)` is empty exactly when `help_path(err)` is `Some`, that is, when the parse failed with a request for help. | Proved | proved | src/LAWS.bend err_text_help; src/LAWS.bend err_text_iff |

### The argument list (SHAKE-ARGS)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| SHAKE-ARGS-1 | The copy `argv` makes of the words `IO.args` gives keeps all of them, in order and unchanged: for every list, reading the copy back gives the list. | Proved | proved | src/LAWS.bend copy_keeps |

## Left to prove

Every pending row is unproved in full, except those below; the RFC's Rollout says in which phase each row's laws land.

| ID | Proved so far | Missing |
| :---- | :---- | :---- |
| SHAKE-TOK-7 | `unknown_long`, `unknown_short`: wherever the words before it leave the walker free, a long or short option that no argument of the walker's current argument list spells fails the parse with `UnknownFlag` of the word, whatever follows. | That the walker's current argument list, after a subcommand is selected, is that subcommand's own, so a parent's arguments are not matched; it is part of SHAKE-PARSE-4. |
| SHAKE-PARSE-10 | `get_last`: `get` reads the value of the last binding of a name, whatever comes before it. | That `parse` records bindings in the order the words give them, which is part of SHAKE-PARSE-1. |

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| SHAKE-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law. | It cannot be checked from inside Bend; this is EZ-TRUST-1. shake pins bend 2.0.26 through the flake. |
| SHAKE-TRUST-2 | A program compiled by bend 2.0.26 hands `IO.args` the process's words after the program name, except that it stops examining words at the first `--`, drops that `--` and passes every later word through unchanged; before that `--` it removes `--threads` and `--gpu` with the word after each, and ends the process before `main` on `--help` and on `--gpu-build`. | It is the C `main` bend emits, read from bend 2.0.26's own source (in its binary) and confirmed against the demo. It changes when bend does, so every bend bump rechecks it. |
| SHAKE-TRUST-3 | The proof-gate runner fails the build unless the first line of `bend src/PROOF.bend` is `All terms check.` | It is ez's `mkProofs` running `ez prove`, run by `nix flake check` in CI; this is EZ-TRUST-4. |
| SHAKE-TRUST-4 | `argv` hands on exactly the list `IO.args` answers, through the copy SHAKE-ARGS-1 is about. | It is IO, which no law can reach: `argv` in `src/args.bend` is one `IO.bind` of `IO.args` into `copy`, short enough to check by reading, and marked `# noqa: L001` for that reason. |
