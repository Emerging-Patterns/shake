# RFC: A Behavioral Specification for shake

Read at `b93357a` on `main` ("chore: bump Bend to 2.0.26 (#13)"), bend 2.0.26, bolt v0.4.0 (pinned), bolt v1.6.2 (current).

## Draft Status

**State:** Accepted. Every review item below is resolved: the maintainer accepted each recommendation.

This draft was written from the code at `b93357a`, from the evidence in [shake-law-inventory.md](shake-law-inventory.md), and from the positions reached by the specifications of ez ([ez-spec.md](https://github.com/Emerging-Patterns/ez/blob/master/docs/rfc/ez-spec.md)) and bolt ([bolt-spec.md](https://github.com/Emerging-Patterns/bolt/blob/v1.6.2/docs/rfc/bolt-spec.md)). Every verdict was checked against the code, and most were confirmed by running the demo binary built from a fresh copy of this tree. The items below are decisions this draft makes and asks a maintainer to confirm. Each one also appears inline where the decision lives. The first two come first because the rest depend on them. REVIEW-2, REVIEW-9 and REVIEW-10 were resolved by the change that moved the code into `src/` behind `main.bend`; the paths below that say `shake/main.bend` are as read at `b93357a` and now live in `src/cli.bend`.

**Items for review:**

- [x] <!-- REVIEW-1 (resolved): The headline guarantee. We propose SHAKE-PARSE-1, value fidelity: in every successful parse of a well-formed spec, each bound value is either a word of argv (or the part of one after `=` or after a short spelling) copied verbatim to the argument that word was given for, or the default of an argument argv did not bind. It is the row whose failure makes shake pointless, and the planted truncation bug in the inventory is exactly what it rules out. The alternatives were a round trip through a new renderer (stronger, but it adds API nobody asked for) and proving only the positional lemmas bolt already needs (too narrow to name the tool's purpose). Decision: the headline guarantee is SHAKE-PARSE-1, value fidelity, as proposed. -->
- [x] <!-- REVIEW-2 (resolved): shake's interface is `main.bend` at the repository root, following ez's project layout and ezjson's rule that consumers import only the entry and trust the internals. `main.bend` names the types as `Data` aliases (`def Cli() -> Data: S.Cli`, so a consumer writes `Shake.Cli`), wraps the builders, `parse`, `get`, `get_all`, `on`, `path_of`, `help`, `err_text` and `argv`, and adds `help_path(err) -> Maybe<List<String>>`, because Bend resolves a constructor only through the module that declares it, so a consumer importing `main.bend` alone cannot match `NeedHelp`. Everything under `src/` (the walker, `St`, `Mode`, `Bind`, `show`, the constructors) carries no promise. Every SHAKE row is stated over `main.bend`'s defs, and its laws import `../main.bend`. bolt, which unfolds `src/cli.bend` today, moves to citing SHAKE rows over `main.bend` when it next bumps shake, and until then keeps BOLT-TRUST-8; the walker's names stay as they are until bolt has moved. Consumers that match `Shake.NeedHelp` (ez) switch to `help_path` when they bump. Decided in the change that moved the code to `src/`. -->
- [x] <!-- REVIEW-3 (resolved): `--` in a compiled binary (inventory F1). bend 2.0.26's runtime consumes the first `--` and passes the rest unexamined, so `parse` only ever sees a second one. We propose no code change: SHAKE-TOK-4 states what `parse` does with a `--` it is given, SHAKE-TRUST-2 states what the runtime does before that, and the README and `main.bend`'s header say plainly that a compiled program's users type `--` twice (`tool add -- -- -5 3`). The alternative, treating the runtime's `--` as ending options by guessing from the words, cannot work: after the runtime has removed it, `tool greet -- --name` and `tool greet --name` are the same list. Asking bend to pass `--` through is a change to another program, and we record it under Future Steps rather than depend on it. Docs-only behavior change. Decision: no code change for `--`; SHAKE-TOK-4 is about what `parse` is given, SHAKE-TRUST-2 states the runtime, and the README and `main.bend` say that users of a compiled program type `--` twice. -->
- [x] <!-- REVIEW-4 (resolved): A repeated option (F4). Today the first value wins for `get`, and `get_all` returns all. We propose the last value wins for `get`, as getopt-style tools do, with `get_all` unchanged, and SHAKE-PARSE-10 states it. clap 4 refuses a repeated single-valued option instead; we do not follow it here because a refusal needs a new `ParseErr` constructor, which REVIEW-2 makes a breaking change for every consumer. Behavior change. Decision: the last value of a repeated option wins for `get`, `get_all` is unchanged; SHAKE-PARSE-10 and SHAKE-GET-1 state it. -->
- [x] <!-- REVIEW-5 (resolved): `-n=Ada` (F7). Today it binds `=Ada`. We propose no change and SHAKE-TOK-2 states the verbatim rule: POSIX getopt binds `=Ada` too, and stripping would make `-n=` ambiguous with an empty value. clap strips the `=`; if the maintainer prefers clap's reading, TOK-2 changes wording and the change lands as its own PR. Decision: no change: `-n=Ada` binds `=Ada`, and SHAKE-TOK-2 states the verbatim rule. -->
- [x] <!-- REVIEW-6 (resolved): `help` with an unknown name (F5). Today `help nope` shows the root page and exits 0, and `help nope greet` shows `greet`'s. We propose `parse` resolves the words after `help` against the subcommand tree and fails with `Unexpected{word}` on the first name that is not a subcommand at that point, as clap does; SHAKE-PARSE-8 and SHAKE-HELP-1 state it. `help` itself keeps its current behavior for a path it is handed, since it is also called by programs with paths they built. Behavior change. Decision: `parse` refuses an unknown name after `help` with `Unexpected{word}`; `help` itself keeps skipping for paths a program builds. -->
- [x] <!-- REVIEW-7 (resolved): Checking a spec (F6). `rest.last` is dead code and nothing else checks a Cli. We propose a new pure `check(app: Cli) -> List<SpecErr>` that reports exactly: a rest positional that is not the last positional of its command; two arguments of one command with the same name, short spelling or long spelling; two subcommands of one command with the same name; a subcommand named `help`; a default outside a nonempty choices list; a required positional after an optional one. `parse` does not call it, so no existing program changes behavior; every SHAKE-PARSE row is stated for specs with `check(app) == []`, and a program that wants the guarantees checks its spec (at start, or in its own gate). `rest.last` is deleted. New API. Decision: `check(app) -> List<SpecErr>` is added as proposed, exported from `main.bend`, not called by `parse`; `rest.last` is deleted. -->
- [x] <!-- REVIEW-8 (resolved): Retiring laws. We propose deleting all 53 closed laws and the 20 quantified laws that are definitional, wiring or wording, with `shake/sample.bend`, in one PR, as bolt did; the inventory's "points toward" column keeps the map. The five quantified lemmas (`looks_flag_long`, `allowed_any`, `get_nil`, `on_nil`, `copy_one`) stay untagged until a tagged proof uses them or they are replaced, and `err_text_help` is tagged as a partial law of SHAKE-ERR-1. Decision: all 53 closed laws and the 20 definitional, wiring and wording laws go with `sample.bend`; the five lemmas stay untagged and `err_text_help` is tagged SHAKE-ERR-1. -->
- [x] <!-- REVIEW-9 (resolved): bolt is pinned as `[tools.bolt]` in ez.toml and ez.lock.toml at `ada294e`, the commit on bolt's main that adds `# noqa: CODE` (BOLT-OUT-7) and is not yet released, and `mkLint` builds it from the lock, so the flake no longer has a bolt input. It re-pins to the first release tag that contains `ada294e`. The style findings of the newer rules (S003, S004) are fixed; `coverage` warns until the laws exist, and IO defs, which no law can reach, carry `# noqa: L001` on their def line (`argv`, and the demo's IO); `closed` and `unsafe` are errors; `trace` is off until SPEC.md lands in phase one and then an error. Asking bolt for a `closed` that sees through unused binders stays open. -->
- [x] <!-- REVIEW-10 (resolved): `show` stays in `src/cli.bend` for the laws and is not in `main.bend`, so it is internal (REVIEW-2); it goes with the closed laws in phase one. -->

## Abstract

shake has 79 laws, all proved by `{==}`. 53 are closed laws carrying an unused `for u: Unit` binder, which is how they pass bolt's `closed` rule; of the other 26, 20 restate definitions and 6 are small lemmas. A parser that truncates every value to six characters passes the gate. This RFC defines a specification for shake in the shape of ez's and bolt's, in which every requirement is **Proved** by a tagged quantified law or **Trusted** as a named assumption; names the headline guarantee, that a successful parse binds every value exactly as the user typed it; fixes what the documentation says about `--` in a compiled program; and settles which of shake's names are its interface, since bolt proves its own laws against shake's internals today.

## Glossary

| Term | Meaning |
| :---- | :---- |
| Cli, Sub, Arg | The spec a program hands shake: the program, its nested commands, and its arguments (`shake/main.bend:15-44`). |
| Flag, option, positional, rest | The four `ArgKind`s: a flag takes no value, an option (`Opt`) takes one, a positional is bound from a plain word by position, a rest positional takes every remaining plain word. |
| Spelling | A short (`-v`) or long (`--verbose`) name an argument is given by. Positionals have none. |
| Binding name | `Arg.name`, the key a value is bound under and read back by. |
| Plain word | An argv word that is `-` or does not start with `-`. |
| Current command | The command whose arguments `parse` is matching words against: the root, then each selected subcommand in turn. |
| Selected path | The subcommand names `parse` walked into, in order (`Matched.path`). |
| Matched | A successful parse: the selected path and the bindings in argv order, defaults after. |
| Well-formed spec | A Cli for which `check` (proposed, REVIEW-7) reports nothing. |
| Runtime | The C `main` bend emits into a compiled program. It sees the process's argv before the program does. |
| Closed law | A law about one fixed input. In shake every closed law has an unused `for u: Unit` binder, so bolt's `closed` rule does not see it. |
| Quantified law | A law whose binders the statement uses. It holds for every input of that type. |
| Proof gate | For every PROOF.bend, `bend PROOF.bend` prints exactly `All terms check.` as its first line. CI runs it through `ez test --unit-only`. |
| Proved | A requirement backed by a quantified law tagged with its ID, passing the proof gate. |
| Trusted | A requirement that is assumed, listed in the trust boundary, and checked by nothing in shake. |
| Pending | The status of a Proved requirement whose law has not landed. A status, not a level. |

## Background

### What shake is

shake is a command-line argument parser for Bend 2, about 1100 lines in `shake/main.bend` plus a 17-line `shake/args.bend`. A program describes itself as a `Cli` value; `parse(app, argv)` returns a `Matched` (the selected command path and the bindings) or a `ParseErr`; `help(app, path)` renders a clap-style usage page; `err_text(app, e)` renders an error. `Args.argv()` is the one IO function: it reads `IO.args()` and copies it into a list the program can read more than once. shake is published on the hub and used by ez and by bolt, the linter the whole family is gated by.

### How shake proves things today

shake has one LAWS.bend with 79 laws and one PROOF.bend in which every proof is `{==}`. The gate passes in about a second, and the pinned bolt reports `clean`. The inventory shows why neither means much. 53 laws state one fixed call: 25 parse a fixed command line against the fixtures in `shake/sample.bend` (21 of them through `show`'s one-line rendering), 6 compare help or error pages byte for byte, and the other 22 pin one helper on one input. Each carries `for u: Unit`, a binder its statement never uses, and that is enough for the `closed` rule of both the pinned bolt and the current one to accept it. Of the 26 laws that really quantify, 20 say that a definition unfolds to its body or how two defs are wired, and the other 6 are small true lemmas. None quantifies over an argv and a spec together.

The consequence is measurable. We changed `parse.put` to keep only the first six characters of every value. The gate printed `All terms check.`, bolt printed `clean`, and the demo printed `hello Alexan` for `greet --name Alexandra`.

### Who depends on shake, and how

ez uses shake the way the README describes: builders, `parse`, `help`, `err_text` and the accessors. bolt uses it differently. bolt's CLI laws (`cli.word_step`, `cli.walk_plain` in `bolt/PROOF.bend`) are proved by unfolding shake's walker step by step, naming ten of its private defs and its `St` and `Mode` types, and bolt's SPEC.md lists shake as BOLT-TRUST-8, "shake v0.1.1 parses argv as its spec says". So the only quantified statements about shake's parser live in another repository, reach into its internals, and rest on a spec that has not been written. That makes this RFC a dependency of bolt's trust boundary as much as a cleanup of shake.

### What the binary does that the documents do not say

Running the demo from a fresh clone found that the compiled runtime handles `--` before shake does. bend 2.0.26's generated `main` copies every word after the first `--` straight through and drops the `--` itself, so `parse` never sees it. The README's promise, and the laws `parse_dash` and `parse_rest_dash`, are true of `parse` and false of the command a user types: `demo greet -- --name` fails, `demo greet -- -- --name` works. The same reading showed that `--gpu-build` is not stripped as the README says but ends the program before `main` runs, and that `--threads` and `--gpu` take the next word with them. The README's build line also fails on a fresh clone because `bin/` does not exist.

## Problem Statement

We need a specification that says, for every behavior shake has, what exactly is guaranteed and whether that is proved for every spec and argv or assumed. When shake's implementation changes, the answer must say mechanically which statements have to survive; and when bolt or ez rely on shake, they must be able to cite those statements instead of unfolding its code.

The goals are one SPEC.md at the repository root with a stable ID and one of two levels per behavior; quantified laws over `parse` for every row that is about parsing; closed laws gone, and kept gone by the linter; a named interface, so a downstream proof has something stable to cite; and documentation that describes what a user of a compiled program experiences.

We are not proving bend, its runtime or its checker correct; those are trust assumptions and the spec names them. We are not making help or error wording contractual: requirements speak about bindings, paths, error constructors and the structure of a help page, never about message text. This RFC does not itself change shake's behavior. Where the spec and the code disagree, the decision is recorded under "Decided behavior changes", and each lands as its own PR.

## Proposal

### Overview

The proposal has the four parts ez and bolt use. A **specification document**, SPEC.md at the repository root, lists every requirement with an ID, a level, a status and its laws. **Law tagging** links each quantified law to the requirement it proves, and bolt's `trace` rule checks the two agree. **Pure decisions**: ez and bolt had to move decisions out of IO into planners before laws could reach them, and shake needs none of that, because `parse`, `help` and `err_text` are already pure functions of their arguments; its only IO is `argv`, whose content is decided by the runtime. A **refactoring contract** says which statements a change may touch.

|  |
|:---:|
| <pre>process argv ──runtime (TRUST-2)──▶ IO.args ──argv (ARGS-1)──▶ parse ──▶ Matched / ParseErr<br>                                                                 (TOK, PARSE rows)</pre> |
| Caption: Everything after `IO.args` is a pure function a law can reach. What the runtime removes before it is one Trusted row. |

### Two levels, and the positions carried over

We take ez's and bolt's positions as settled. A requirement is **Proved** when a quantified law in a LAWS.bend carries its ID as a `# <ID>` line in the comment block above `law` and passes the proof gate. A requirement is **Trusted** when it is a named assumption in the trust boundary. **Pending** is a status of a Proved row whose law has not landed. Closed laws have no standing, tests and fixtures are never evidence, untagged quantified laws are allowed and protected by nothing, and a guarantee proved in a pinned dependency is Trusted from the depending side. shake has no dependencies, so the last point applies the other way: once shake's rows are proved, bolt's BOLT-TRUST-8 can name them.

We use "well-formed" as a premise throughout the parse rows (REVIEW-7). Stating the rows for every Cli would make them false for specs that contradict themselves (two options spelled `-n`), and those specs are the program author's bug, not a parse the user can cause.

### The proof gate

Unchanged: `ez test --unit-only` in `flake.nix`'s `proofs` check, which requires the exact first line `All terms check.` from every PROOF.bend. We confirmed ez's runner at `13e86ea` compares the first line, not the exit status.

### Requirements

The Law cells below are sketches. Names that exist today are real; `check`, `SpecErr`, `pieces` and `defaults_of` do not exist yet and are defined by the laws that introduce them.

#### How a word is read (SHAKE-TOK)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-TOK-1 | A word that starts with `--`, is not exactly `--`, and has at least one char before its first `=` is a long option: the chars between `--` and the first `=` (or the end) are its spelling, and when there is an `=` everything after it, verbatim and possibly empty, is its value. A word `--=...` is refused as `UnknownFlag{word}`. | Proved |
| SHAKE-TOK-2 | A word that starts with `-`, is not `-` and does not start with `--` is a short option: its second char is the spelling, and the rest of the word, verbatim, is its value when it is not empty. | Proved |
| SHAKE-TOK-3 | `-` alone, and every word that does not start with `-`, is a plain word. | Proved |
| SHAKE-TOK-4 | When a word exactly `--` reaches `parse` in option position, it binds nothing and every later word is read as a plain word bound to a positional, whatever its shape. | Proved |
| SHAKE-TOK-5 | A flag given a value (`--verbose=x`, `-vx`) is refused as `Unexpected{word}`. | Proved |
| SHAKE-TOK-6 | An option given no value in its own word takes the next word as its value, unless that word is flag-shaped (starts with `-` and is not `-`) or there is none; then the parse fails with `Missing{name}`. | Proved |
| SHAKE-TOK-7 | A long or short spelling that no argument of the current command has is refused as `UnknownFlag{word}`. Arguments of a parent command are not matched after a subcommand is selected. | Proved |

Evidence: `cut_eq` and `short_of` (`main.bend:153-186`), `parse.step.kind.go` (`main.bend:675-683`), `parse.take_flag` (`main.bend:470-478`), `parse.step.need` (`main.bend:725-732`), `parse.take_arg` (`main.bend:506-516`), and the confirmed runs in the inventory. TOK-7's second sentence is today's behavior, and clap's for non-global arguments: `by_long` and `by_short` search `args`, which `parse.enter` sets to the subcommand's own arguments.

Law sketch for TOK-1, over every well-formed spec, argv prefix and value: `parse(app, pre ++ ["--" ++ s ++ "=" ++ v] ++ post)` binds `v` to the option spelled `s`, when the prefix leaves the walker in a state where `s` is an option of the current command. The laws for TOK-1, TOK-2 and TOK-6 share one lemma about `cut_eq` over every string (`cut_eq(n ++ "=" ++ v) == (n, Some{v})` when `n` has no `=`), which replaces the closed `cut_eq_plain` and `cut_eq_value`.

#### What a parse binds (SHAKE-PARSE)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-PARSE-1 | For every well-formed spec and argv, when `parse` succeeds, every bound value is either a value-carrying piece of argv (a plain word bound to a positional, the value part of an option word, or the word after an option) bound under the name of the argument it was given for, verbatim, or the default of an argument on the selected path that argv did not bind. The number of non-default bindings equals the number of value-carrying pieces. | Proved |
| SHAKE-PARSE-2 | Plain words that select no subcommand bind the current command's positionals in spec order, one word each; a plain word with no positional left is refused as `Unexpected{word}`. | Proved |
| SHAKE-PARSE-3 | A rest positional binds every remaining plain word that selects no subcommand, in argv order, each under the rest's name. | Proved |
| SHAKE-PARSE-4 | Before `--`, a plain word that names a subcommand of the current command selects it: the selected path gains that name, its arguments become current, and bindings made so far are kept. When a required positional of the current command is still unbound, the parse fails with `Missing{name}` of the first such one instead. | Proved |
| SHAKE-PARSE-5 | A value given to an argument with a nonempty choices list binds only when it is in the list, and otherwise fails with `BadValue{name, value}`. An argument with no choices accepts every value. | Proved |
| SHAKE-PARSE-6 | After the last word, each argument of every command on the selected path that argv left unbound and that has a default is bound to its default. A bound argument's value is never replaced, and no argument without a default gains a binding. | Proved |
| SHAKE-PARSE-7 | A successful parse binds every required argument of every command on the selected path. Otherwise the parse fails with `Missing{name}`. | Proved |
| SHAKE-PARSE-8 | Before `--` and before any positional of the current command is bound, a plain word `help` makes the parse fail with `NeedHelp{path}`, where `path` is the selected path followed by the remaining words, each of which names a subcommand under the one before; a remaining word that does not fails with `Unexpected{word}`. | Proved |
| SHAKE-PARSE-9 | Once a word makes the parse fail, the words after it do not change the error. | Proved |
| SHAKE-PARSE-10 | When an option or flag is given more than once, `get` reads the last value given and `get_all` every value, in argv order. | Proved |

Evidence: `parse.take_pos` (`main.bend:571-580`) and `parse.take_pos.keep`; `parse.word.go` and `parse.enter_or` (`main.bend:625-643`); `allowed` (`main.bend:347-348`) and `parse.take_opt_val`; `fill.args` and `miss.args` (`main.bend:787-815`); `parse.step.help` and the `Help{}` arm of `parse.step.mode`; the `Dead{e}` arm of `parse.step.mode` (`main.bend:739-740`). PARSE-8's last clause depends on REVIEW-6, and PARSE-10 on REVIEW-4: both rows stay pending until their change lands.

PARSE-1 is the headline guarantee (REVIEW-1). Its law sketch, with `pieces(app, argv)` defined as the value-carrying pieces in order and `defaults_of(app, m)` as the default bindings `fill.args` added:

```
# LAW: every bound value was typed by the user, or is a default nothing overrode
# SHAKE-PARSE-1
law fidelity:
  for app: Shake.Cli
  for argv: List<&2, String>
  for m: Shake.Matched
  for ok: {Shake.check(app) == [] : List<&2, Shake.SpecErr>}
  for hit: {Shake.parse(app, argv) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {binds_of(m) == pieces(app, argv) ++ defaults_of(app, m) : List<&2, Shake.Bind>}
```

It is proved by induction over argv with the walker state as the invariant, reusing PARSE-2, PARSE-3 and TOK-1 to TOK-6 as the step lemmas. It is also the row a truncation, a dropped word or a value bound to the wrong name breaks, which the closed laws could not see. PARSE-9 is a frame law and the cheapest row: it follows from the `Dead` arm by induction over the remaining words.

PARSE-2 and PARSE-3 are the facts bolt proves today by unfolding shake (`cli.word_step`, `cli.walk_plain`). Stated over `parse` instead of the walker, they are what bolt should cite (REVIEW-2).

#### Checking a spec (SHAKE-SPEC)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-SPEC-1 | `check(app)` reports exactly one `SpecErr` for each of: a rest positional that is not its command's last positional; a second argument of one command with a name, short spelling or long spelling an earlier one has; a second subcommand of one command with an earlier one's name; a subcommand named `help`; a default outside its argument's nonempty choices; a required positional after an optional one. It reports nothing else. | Proved |

This is new API (REVIEW-7). Its laws are completeness as a count equality and a frame law (a spec with none of the patterns gets `[]`), the shape bolt uses for its rules.

#### Reading a result (SHAKE-GET)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-GET-1 | For every Matched and name: `get` is the value of the last binding with that name, or `""` when there is none; `get_all` is the values of every binding with that name, in binding order; `on` is true exactly when `get` is `"true"`; `path_of` is the selected path. | Proved |

GET-1 is pure list reasoning and one of the first rows to prove. Its first clause changes from "first" to "last" with REVIEW-4, and stays pending until then. The empty string for "not bound" and for "bound to empty" (F10) is stated rather than changed: telling them apart needs a new accessor, which we list under Future Steps.

#### Help pages (SHAKE-HELP)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-HELP-1 | `help(app, path)` renders the page of the command reached by following each name of `path` from the root through the subcommands, skipping a name that is not a subcommand where it stands. | Proved |
| SHAKE-HELP-2 | A page lists each subcommand of its command exactly once, in spec order, followed by `help`, and each flag and option exactly once, in spec order. Its usage line names each positional exactly once, in spec order, as `<NAME>` when required and `[NAME]` otherwise, with `...` after a rest positional. | Proved |

Wording, padding and the title line are not requirements. The six closed laws that pin whole pages are deleted, and the laws for HELP-2 count occurrences, so the layout can change without touching a law. HELP-1 keeps today's skipping because `help` is also called with paths a program builds; the refusal of an unknown name happens earlier, in `parse` (REVIEW-6).

#### Errors (SHAKE-ERR)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-ERR-1 | `err_text(app, e)` is empty exactly when `e` is `NeedHelp`. | Proved |

`err_text_help` already proves half of this over every Cli and path; the other half is a case split over the constructors. The wording of each message, and that it shows the root usage line (F8), are not requirements.

#### The argument list (SHAKE-ARGS)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| SHAKE-ARGS-1 | `copy` preserves every list word for word: it has the same length, and the same word at every index. `argv` is `IO.args` passed through `copy`. | Proved |

The `&1` and `&2` lists are different types, so the law compares them through `String.join` and `List.length` rather than `==`; `copy_one` becomes the step case of its induction.

#### Trust boundary

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| SHAKE-TRUST-1 | The Bend checker is sound: a PROOF.bend that prints `All terms check.` proves its laws. | The checker is the gate; nothing inside shake can check it. |
| SHAKE-TRUST-2 | A program compiled by bend 2.0.26 hands `IO.args` the process's words after the program name, except that it stops examining words at the first `--`, drops that `--` and passes every later word through unchanged; before that `--` it removes `--threads` and `--gpu` with the word after each; and it ends the process before `main` on `--help` and on `--gpu-build`. | It is the runtime bend emits, read from bend 2.0.26's own source (in its binary) and confirmed against the demo. It changes when bend changes, so every bend bump rechecks it. |
| SHAKE-TRUST-3 | The proof-gate runner fails any PROOF.bend whose first line is not exactly `All terms check.` | ez's `ez test` at the pinned revision; it is another project's code. |

The trust boundary is small because shake has almost no IO. TRUST-2 is the row a user of a compiled program most needs to read, and the README should point to it.

### Retiring laws

Following bolt (REVIEW-8), all 53 closed laws go in one PR, with the 20 quantified laws that only unfold a definition, restate wiring or pin `show`'s format, and with `shake/sample.bend` and `show`, which only they use (REVIEW-10). The inventory's "points toward" column is the map for their replacements. Five quantified lemmas stay, untagged, until a tagged proof uses them: `looks_flag_long` (TOK-6), `allowed_any` (PARSE-5), `get_nil` and `on_nil` (GET-1), `copy_one` (ARGS-1). `err_text_help` is tagged SHAKE-ERR-1 as a partial law.

### Tagging and traceability

SHAKE rows use bolt's SPEC.md format exactly: tables headed `| ID | Requirement | Level | Status | Law |`, the Law cell as `<path> <law>` entries joined by `; `, a pending row allowed to name tagged partial laws with a "Left to prove" section, and the trust table headed `| ID | Assumption | Why it is trusted |`. bolt v1.6.2's `trace` rule checks it, so the bolt pin moves to v1.6.2 before SPEC.md lands (REVIEW-9).

### The refactoring contract

A tagged law's statement changes only when its SPEC.md row changes, and that is a behavior change the PR says it is. `main.bend` is the interface (REVIEW-2): removing or retyping one of its defs is a breaking change. Untagged laws, proofs and everything under `src/` may change freely, with one temporary exception: until bolt cites SHAKE rows instead of unfolding `src/cli.bend`'s walker, a change to the walker's names or shapes is a breaking change for bolt, and the PR says so.

### Decided behavior changes

Each lands as its own PR, checked against master's demo binary, and a row that depends on one stays pending until it lands.

| Change | Rows | Kind |
| :---- | :---- | :---- |
| README: create `bin/` before the build line (F2) | none | docs |
| README and `main.bend` header: in a compiled program the runtime takes the first `--`, so users type it twice; `--gpu-build` ends the program; `--threads` and `--gpu` take the next word (F1, REVIEW-3) | SHAKE-TOK-4, SHAKE-TRUST-2 | docs |
| The last value of a repeated option wins for `get` (F4, REVIEW-4) | SHAKE-PARSE-10, SHAKE-GET-1 | behavior |
| `parse` refuses an unknown name after `help` (F5, REVIEW-6) | SHAKE-PARSE-8 | behavior |
| `check` and `SpecErr` added, `rest.last` removed (F6, REVIEW-7) | SHAKE-SPEC-1, and the premise of every PARSE row | new API |
| `show` moves out of `main.bend` (REVIEW-10) | none | API removal |

Not changed, with the reason recorded: `-n=Ada` keeps binding `=Ada` (REVIEW-5); the error text keeps showing the root usage line and keeps reporting a missing option value as a missing argument, since both are wording (F8, F9); an empty value and no value keep reading the same through `get` (F10).

### How we will know it worked

The gate passing will mean something: the truncation bug from the inventory, and any bug that binds a value the user did not type or to a name it was not given for, fails PARSE-1's proof. bolt's `trace` reports nothing at error, and `closed` reports nothing because no closed law is left. bolt's BOLT-TRUST-8 names SHAKE rows, and bolt's CLI proofs cite shake's laws instead of shake's walker.

## Abandoned Ideas

**Keep the closed laws as `# toward` trails.** ez did this for a while under bolt v0.9.0. It kept ez on an old bolt, and ez deleted the trails once the replacing laws were written down. shake's closed laws encode one accident each (the fixture parse through `show`, pages byte for byte), and the inventory keeps the map, so the trails would tell nobody anything.

**Prove each fixture command line.** Stating `parse(Sample.spec(), ["greet", "--name", "Ada"])` for more command lines is the same closed law at a larger count. It is what we have, and the planted bug shows what it misses.

**Prove shake equal to a reference parser.** A second implementation shares the first's reading of the corner cases, which is where every accident in the inventory lives. bolt and ez both deleted their refactor-equivalence laws for this reason.

**Make help and error wording contractual.** It is what users see, which argues for it. But no program depends on the bytes, a wording change would break every such law, and the six page laws show the cost. The rows state structure (every subcommand listed once, in order) instead.

**Refuse ill-formed specs inside `parse`.** It would make every row unconditional. It needs a new `ParseErr` constructor, which breaks consumers that match on it, and it charges every parse for a check a program can make once.

**Handle the runtime's `--` inside shake.** After the runtime removes it, the words a program gets from `greet -- --name` and `greet --name` are identical, so no rule in `parse` can recover the difference.

## Risks

**Proof effort for PARSE-1.** The walker threads ten values through every step, and the headline law needs an invariant over all of them. We plan a spike first: prove PARSE-2 over `parse` for every well-formed spec, which exercises the same induction on the simplest arm, before designing the PARSE-1 proof. If it proves too expensive, the row moves to Trusted with a written reason, which is a visible weakening the maintainer approves.

**Breaking bolt.** Restructuring the walker to make the proofs easier would break bolt's proofs on its next pin bump. The contract keeps the walker's names until bolt migrates, and the rollout sequences bolt's migration right after PARSE-2 and PARSE-3 land.

**The runtime changes.** TRUST-2 is true of bend 2.0.26. A bend release could pass `--` through, and then the README's advice to type it twice would bind a literal `--`. Every bend bump rechecks TRUST-2 against the new runtime.

**Encoding accidents as requirements.** TOK-7's scoping and F11's rule that a subcommand name always selects are today's behavior. We keep them because clap behaves the same and consumers already rely on them; a row is a promise, and the maintainer should strike any row that promises more than they want to keep.

**Checker soundness.** TRUST-1, as in ez and bolt.

## Rollout

Each phase leaves the gate green, bolt clean at the pinned version, and SPEC.md honest about what is pending.

| Phase | What lands | What is true after |
| :---- | :---- | :---- |
| Preliminary | this RFC and the inventory (no code change); the two docs changes | the README builds from a fresh clone and describes `--` as users meet it |
| Zero (done) | the code moved to `src/` behind `main.bend`; ez at `df6d616`; bolt at `ada294e` as a `[tools.bolt]` pin, its style findings fixed, `coverage` at warn with `# noqa: L001` on IO | the tree is clean under a bolt that has `trace` and `noqa` |
| One | SPEC.md from this RFC; 73 laws, `sample.bend` and `show` deleted; `err_text_help` tagged; `trace` at error; `closed` at error | every row is pending or trusted, and the gate stops pretending |
| Two | the cheap rows: PARSE-9 (frame), ERR-1, GET-1 (after REVIEW-4's change), ARGS-1, PARSE-5, TOK-3, TOK-5, TOK-7 | the first proved rows |
| Three | the spike, then PARSE-2 and PARSE-3; bolt bumps shake and cites them; then TOK-1, TOK-2, TOK-4, TOK-6, PARSE-4, PARSE-6, PARSE-7, PARSE-8 | BOLT-TRUST-8 names SHAKE rows |
| Four | `check` and SPEC-1; then PARSE-1; then HELP-1 and HELP-2; `coverage` back at error | no pending rows; the inventory is folded into this RFC and deleted |

The finish line: no pending rows, every closed law deleted, `trace`, `closed` and `coverage` at error, and bolt citing shake's laws rather than its walker.

## Future Steps

**Tell "unset" from "empty".** A `find(m, name) -> Maybe<String>` accessor would let a program tell `--name=` from no `--name`. It is new API and nobody has asked for it.

**Ask bend to pass `--` through.** If the runtime left `--` in the list when it follows the program's own words, shake's `--` would work with one dash-dash. That is a change to bend's runtime and to every compiled Bend program, so we record it rather than depend on it.

**Siblings.** ez's CLI would gain the same guarantees by citing SHAKE rows in its own spec, and a strict `closed` that sees through unused binders (REVIEW-9) protects every repository in the family from shake's pattern.
