# shake law inventory

Read at `b93357a` on `main` ("chore: bump Bend to 2.0.26 (#13)"), with bend 2.0.26 (the release `flake.lock` pins through `bendlang/bend` at `6a77e12`), bolt v0.4.0 (`flake.lock` pins `Emerging-Patterns/bolt` at `24b497e`) and ez at `13e86ea`.

This is the companion to [shake-spec.md](shake-spec.md). Since it was read, the code has moved: `shake/main.bend` is `src/cli.bend` (its one-letter parameters doubled and its headers rewrapped for bolt's style rules, with no other change), `shake/args.bend`, `LAWS.bend`, `PROOF.bend` and `sample.bend` are under `src/`, and `main.bend` at the root is the interface. Paths and line numbers below are as read. It records what `shake/LAWS.bend` states today, maps each law to the requirement it points toward, and records what we found by reading the code and running a binary built from this tree. It follows the shape of bolt's [bolt-law-inventory.md](https://github.com/Emerging-Patterns/bolt/blob/v1.6.2/docs/rfc/bolt-law-inventory.md) and takes the positions ez's and bolt's specifications reached: exactly two assurance levels, Proved and Trusted; pending is a status, not a level; a closed law has no standing; a test or fixture is never evidence for a requirement.

## How we ran things

The proof gate is `bend shake/PROOF.bend` from the repository root, the same check `ez test --unit-only` makes in CI through ez's `mkProofs` (ez's runner compares the first line with `All terms check.`, so a proof that leans on unsafe code fails it). The linter is the pinned bolt, built with `bend bolt/main.bend -o bin/bolt.bin` at `24b497e` and run with no arguments at the root. We also built bolt v1.6.2, the current release, to see what the rollout's first lint bump will report; its hub dependencies were filled into a local `BEND_LIB` from the git revisions in bolt's `ez.toml`, because this environment cannot reach `hub.bend-lang.com`. The demo binary was built from a fresh copy of the tracked files (`git archive HEAD`), following the README.

## How to read the tables

**Kind** is `Q` for a quantified law whose binders the statement uses, and `C` for a closed law. shake writes no law without a binder: each of its 53 closed laws has exactly one binder, `for u: Unit`, that the statement never mentions. We count those as `C`, because they state one fixed input, and the table marks them `C (u)` so the disguise is visible.

**Proof** is `{==}` when the whole proof in PROOF.bend is `{==}`: the two sides reduce to the same term with no case split. Every one of shake's 79 proofs is `{==}`. For a closed law that is what a closed law is. For a quantified law it means the binders are never inspected, so the law restates how a definition unfolds on its first step.

**Claim** is what the law states, in one line, about the input it is really about.

**Points toward** names the requirement in the RFC the law illustrates. For a law we propose to delete, it records where the replacing quantified law belongs. `none` has a reason in parentheses: `definitional` restates a definition, `wiring` restates how two defs compose, `helper pin` is one private helper on one input, `wording` pins text nobody depends on, `fixture` is a law about test scaffolding, `dead code` is about a def nothing calls.

## Proposed requirement IDs

These are the IDs the RFC proposes. They are listed here so the tables can point at them; their wording and verdicts are in the RFC.

| ID | Short name |
| :---- | :---- |
| SHAKE-TOK-1 | A word starting `--` is a long option: the spelling up to the first `=`, and the rest after it as a value, verbatim. |
| SHAKE-TOK-2 | A word starting with one `-` (not `-` alone) is a short option: one char of spelling, the rest as a glued value. |
| SHAKE-TOK-3 | `-` alone, and every word not starting with `-`, is a plain word. |
| SHAKE-TOK-4 | After a word exactly `--` reaches `parse`, every later word is a positional value, verbatim. |
| SHAKE-TOK-5 | A flag given a value is refused. |
| SHAKE-TOK-6 | An option with no glued value takes the next word, unless that word is flag-shaped or there is none. |
| SHAKE-TOK-7 | A spelling no argument of the current command has is refused as unknown. |
| SHAKE-PARSE-1 | Value fidelity, the headline guarantee: every bound value is a word of argv, verbatim, or a default. |
| SHAKE-PARSE-2 | Plain words bind the current command's positionals in spec order. |
| SHAKE-PARSE-3 | A rest positional binds every remaining plain word, in order. |
| SHAKE-PARSE-4 | A plain word naming a subcommand selects it. |
| SHAKE-PARSE-5 | A value outside an argument's nonempty choices is refused. |
| SHAKE-PARSE-6 | Defaults fill exactly the unbound arguments that have one. |
| SHAKE-PARSE-7 | A successful parse binds every required argument on the selected path. |
| SHAKE-PARSE-8 | `help` in command position asks for help on the words after it. |
| SHAKE-PARSE-9 | The first error wins. |
| SHAKE-PARSE-10 | A repeated option (decided behavior change). |
| SHAKE-SPEC-1 | `check` reports exactly the ways a Cli is ill-formed (new). |
| SHAKE-GET-1 | `get`, `get_all`, `on` and `path_of` read the Matched as stated. |
| SHAKE-HELP-1 | `help` shows the page of the command its path names. |
| SHAKE-HELP-2 | A page lists every subcommand and every option once, in spec order, and the usage line every positional. |
| SHAKE-ERR-1 | `err_text` is empty exactly for NeedHelp. |
| SHAKE-ARGS-1 | `argv` is the runtime's argument list, word for word. |
| SHAKE-TRUST-1 | The Bend checker is sound. |
| SHAKE-TRUST-2 | The compiled runtime's argument handling, as bend 2.0.26 does it. |
| SHAKE-TRUST-3 | The proof-gate runner reads the first line. |

## The gate and the linter on shake itself

| Check | Result | Time |
| :---- | :---- | :---- |
| `bend shake/PROOF.bend` | first line `All terms check.`, exit 0 | 1.1 s |
| pinned bolt v0.4.0, whole tree | `clean`, exit 0 | 0.7 s |
| bolt v1.6.2, whole tree, shake's bolt.bend | 140 errors: 82 S004 (`param`, one-letter parameters), 51 S003 (`wrap`, wrapped headers), 7 L001 (`coverage`, every def of `examples/demo/main.bend`); 0 L002 (`closed`) | 0.8 s |
| bolt v1.6.2 `trace` | not run: shake has no SPEC.md | |

Both green results mean less than they sound, for the same reason. bolt's `closed` rule (L002 in v1.6.2, `closed` in v0.4.0) reports a law with no `for` or `exs` line, and every closed law in shake has one: `for u: Unit`, which nothing uses. So the rule that exists to reject closed laws accepts all 53, in the pinned bolt and in the current one. `coverage` is satisfied the same way: every def in `shake/main.bend` is named by some law, and for most of them that law is one computed case. bolt's own inventory warned that a `for` binder the statement never uses makes a closed law look quantified; shake is the case at scale.

We checked the gate directly by planting a bug. Changing `parse.put` to bind `String.take(val, 6n)` instead of `val` truncates every bound value to six characters. The gate still printed `All terms check.`, and the demo built from that tree printed `hello Alexan` for `greet --name Alexandra`. Every fixture value in LAWS.bend is six characters or fewer. We restored the file before going on.

## Summary

| File | Laws | Quantified | Closed | Quantified proved by `{==}` | Pin wording |
| :---- | :---- | :---- | :---- | :---- | :---- |
| `shake/LAWS.bend` | 79 | 26 | 53 | 26 | 6 |

"Pin wording" counts closed laws whose expected value is help or error text (`help_root`, `help_greet`, `help_add`, `help_rest`, `help_rest_req`, `err_text_unknown`). A further 21 compare `show`'s one-line rendering of a fixture parse, and `show` exists only for the laws.

**What shake proves today.** Nothing about parsing. Of the 26 quantified laws, 20 restate a definition's first unfolding, how two defs are wired, or `show`'s format (a builder is its constructor, `parse` is `finish` of `walk`, a lookup in an empty list is `None`), 5 are small lemmas that are true and could serve a requirement (`looks_flag_long`, `allowed_any`, `get_nil`, `on_nil`, `err_text_help`), and 1 is one step of a copy (`copy_one`). No law quantifies over an argv and a spec together, which is where every behavior a caller relies on lives. The 53 closed laws check that about thirty fixed command lines still parse and render as they did. The quantified content about shake's parser that does exist lives in bolt: bolt's `bolt/PROOF.bend` proves `cli.word_step` and `cli.walk_plain`, that a plain word binds the next positional and that plain words fill a rest positional in order, by unfolding shake's private walker. bolt's SPEC.md lists shake as BOLT-TRUST-8, "shake v0.1.1 parses argv as its spec says", and shake has no spec.

## Inventory

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| `app_is_cli` | Q | `{==}` | `app` builds the Cli of its fields | none (definitional) |
| `sub_is_sub` | Q | `{==}` | `sub` builds the Sub of its fields | none (definitional) |
| `flag_is_arg` | Q | `{==}` | `flag` builds a Flag Arg, not required, no default, no choices | none (definitional) |
| `opt_is_arg` | Q | `{==}` | `opt` builds an Opt Arg of its fields | none (definitional) |
| `pos_is_arg` | Q | `{==}` | `pos` builds a Pos Arg with no spellings | none (definitional) |
| `rest_is_arg` | Q | `{==}` | `rest` builds a Rest Arg with no spellings | none (definitional) |
| `looks_flag_is_dash` | Q | `{==}` | `looks_flag` is its body | none (definitional) |
| `looks_flag_long` | Q | `{==}` | every word starting `--` is flag-shaped | SHAKE-TOK-6 (lemma) |
| `looks_flag_alone` | C (u) | `{==}` | `-` is not flag-shaped | SHAKE-TOK-6 |
| `cut_eq_is_go` | Q | `{==}` | `cut_eq` is its body | none (definitional) |
| `cut_eq_plain` | C (u) | `{==}` | `cut_eq("name")` has no value | SHAKE-TOK-1 |
| `cut_eq_value` | C (u) | `{==}` | `cut_eq("name=Ada")` splits at `=` | SHAKE-TOK-1 |
| `short_of_is_take` | Q | `{==}` | `short_of` is its body | none (definitional) |
| `short_of_glued` | C (u) | `{==}` | `short_of("nAda")` is `n` and `Ada` | SHAKE-TOK-2 |
| `short_of_one` | C (u) | `{==}` | `short_of("n")` has no value | SHAKE-TOK-2 |
| `by_long_nil` | Q | `{==}` | no long spelling in an empty list | none (definitional) |
| `by_long_flag` | C (u) | `{==}` | one fixed flag is found by `verbose` | SHAKE-TOK-1 |
| `by_short_nil` | Q | `{==}` | no short spelling in an empty list | none (definitional) |
| `by_short_flag` | C (u) | `{==}` | one fixed flag is found by `v` | SHAKE-TOK-2 |
| `by_name_nil` | Q | `{==}` | no name in an empty list | none (definitional) |
| `by_name_flag` | C (u) | `{==}` | one fixed flag is found by `verbose` | none (helper pin) |
| `find_sub_nil` | Q | `{==}` | no Sub in an empty list | none (definitional) |
| `find_sub_head` | C (u) | `{==}` | one fixed Sub is found by name | SHAKE-PARSE-4 |
| `pos_of_nil` | C (u) | `{==}` | an empty spec has no positionals | none (helper pin) |
| `pos_of_keeps` | C (u) | `{==}` | one fixed spec keeps its positional and drops its flag | SHAKE-PARSE-2 |
| `pos_of_rest` | C (u) | `{==}` | one fixed spec keeps its rest positional | SHAKE-PARSE-3 |
| `rest_last_none` | C (u) | `{==}` | `rest.last` of one positional | none (dead code) |
| `rest_last_ok` | C (u) | `{==}` | `rest.last` with rest at the end | none (dead code) |
| `rest_last_mid` | C (u) | `{==}` | `rest.last` with rest in the middle | none (dead code); SHAKE-SPEC-1 |
| `allowed_any` | Q | `{==}` | empty choices accept every value | SHAKE-PARSE-5 (lemma) |
| `allowed_listed` | C (u) | `{==}` | `red` is among `red, green` | SHAKE-PARSE-5 |
| `allowed_other` | C (u) | `{==}` | `blue` is not among `red, green` | SHAKE-PARSE-5 |
| `bound_nil` | Q | `{==}` | nothing is bound in an empty list | none (definitional) |
| `bound_head` | C (u) | `{==}` | one fixed bind is bound | none (helper pin) |
| `get_nil` | Q | `{==}` | `get` on an empty Matched is `""` | SHAKE-GET-1 (lemma) |
| `get_head` | C (u) | `{==}` | `get` reads one fixed bind | SHAKE-GET-1 |
| `get_all_nil` | Q | `{==}` | `get_all` on an empty Matched is empty | none (definitional) |
| `get_all_two` | C (u) | `{==}` | `get_all` of two fixed binds | SHAKE-GET-1 |
| `on_nil` | Q | `{==}` | no flag is on in an empty Matched | SHAKE-GET-1 (lemma) |
| `on_true` | C (u) | `{==}` | one fixed flag bound to `true` is on | SHAKE-GET-1 |
| `path_of_keeps` | Q | `{==}` | `path_of` returns the path field | none (definitional) |
| `parse_is_walk` | Q | `{==}` | `parse` is `finish` of `walk` of `start` | none (wiring) |
| `show_done` | Q | `{==}` | `show` of a Done is `ok` and the match | none (wording) |
| `show_fail` | Q | `{==}` | `show` of a Fail is `err` and the tag | none (wording) |
| `help_is_go` | Q | `{==}` | `help` is `help.go` from the root page | none (wiring) |
| `err_text_help` | Q | `{==}` | NeedHelp's error text is empty for every Cli and path | SHAKE-ERR-1 |
| `parse_flag_long` | C (u) | `{==}` | `--verbose greet` on the fixture | SHAKE-TOK-1 |
| `parse_flag_short` | C (u) | `{==}` | `-v greet` on the fixture | SHAKE-TOK-2 |
| `parse_opt_long` | C (u) | `{==}` | `greet --name Ada` on the fixture | SHAKE-TOK-6 |
| `parse_opt_eq` | C (u) | `{==}` | `greet --name=Ada` on the fixture | SHAKE-TOK-1 |
| `parse_opt_short` | C (u) | `{==}` | `greet -n Ada` on the fixture | SHAKE-TOK-6 |
| `parse_opt_glued` | C (u) | `{==}` | `greet -nAda` on the fixture | SHAKE-TOK-2 |
| `parse_pos` | C (u) | `{==}` | `greet Ada` on the fixture | SHAKE-PARSE-2 |
| `parse_default` | C (u) | `{==}` | `greet` fills `name=world` | SHAKE-PARSE-6 |
| `parse_add` | C (u) | `{==}` | `add 2 3` on the fixture | SHAKE-PARSE-2 |
| `parse_nested` | C (u) | `{==}` | `add 2 3 more` selects `add/more` | SHAKE-PARSE-4 |
| `parse_dash` | C (u) | `{==}` | `greet -- --name` binds `who=--name` | SHAKE-TOK-4 |
| `err_missing` | C (u) | `{==}` | `add 2` is missing `b` | SHAKE-PARSE-7 |
| `err_choice` | C (u) | `{==}` | `--color purple` is refused | SHAKE-PARSE-5 |
| `err_unknown_long` | C (u) | `{==}` | `--nope` is unknown | SHAKE-TOK-7 |
| `err_unknown_short` | C (u) | `{==}` | `-z` is unknown | SHAKE-TOK-7 |
| `err_help_root` | C (u) | `{==}` | `help` is NeedHelp at the root | SHAKE-PARSE-8 |
| `err_help_greet` | C (u) | `{==}` | `help greet` is NeedHelp at `greet` | SHAKE-PARSE-8 |
| `err_unexpected` | C (u) | `{==}` | `greet Ada extra` is unexpected `extra` | SHAKE-PARSE-2 |
| `parse_rest_none` | C (u) | `{==}` | no words bind no files | SHAKE-PARSE-3 |
| `parse_rest_one` | C (u) | `{==}` | one word binds one file | SHAKE-PARSE-3 |
| `parse_rest_many` | C (u) | `{==}` | two words bind two files in order | SHAKE-PARSE-3 |
| `parse_rest_dash` | C (u) | `{==}` | `-- --name a.bend` binds both as files | SHAKE-TOK-4 |
| `err_rest_missing` | C (u) | `{==}` | a required rest with no words is missing | SHAKE-PARSE-7 |
| `show_rest_many` | C (u) | `{==}` | `show` of a two-file parse | none (wording) |
| `help_root` | C (u) | `{==}` | the fixture's root page, byte for byte | SHAKE-HELP-2 (wording) |
| `help_greet` | C (u) | `{==}` | the fixture's `greet` page, byte for byte | SHAKE-HELP-2 (wording) |
| `help_add` | C (u) | `{==}` | the fixture's `add` page, byte for byte | SHAKE-HELP-2 (wording) |
| `help_rest` | C (u) | `{==}` | the rest fixture's page, byte for byte | SHAKE-HELP-2 (wording) |
| `help_rest_req` | C (u) | `{==}` | one required rest renders `<FILES>...` | SHAKE-HELP-2 |
| `err_text_unknown` | C (u) | `{==}` | the text for `--nope`, byte for byte | SHAKE-ERR-1 (wording) |
| `copy_nil` | C (u) | `{==}` | `copy` of the empty list | SHAKE-ARGS-1 |
| `copy_one` | Q | `{==}` | `copy` of a one-word list | SHAKE-ARGS-1 |
| `argv_is_copy` | C (u) | `{==}` | `argv` is its body | none (definitional) |

## Coverage by requirement

| Requirement | Laws pointing toward it | Quantified among them |
| :---- | :---- | :---- |
| SHAKE-TOK-1 | `cut_eq_plain`, `cut_eq_value`, `by_long_flag`, `parse_flag_long`, `parse_opt_eq` | none |
| SHAKE-TOK-2 | `short_of_glued`, `short_of_one`, `by_short_flag`, `parse_flag_short`, `parse_opt_glued` | none |
| SHAKE-TOK-3 | none | none |
| SHAKE-TOK-4 | `parse_dash`, `parse_rest_dash` | none |
| SHAKE-TOK-5 | none | none |
| SHAKE-TOK-6 | `looks_flag_long`, `looks_flag_alone`, `parse_opt_long`, `parse_opt_short` | `looks_flag_long` (a lemma) |
| SHAKE-TOK-7 | `err_unknown_long`, `err_unknown_short` | none |
| SHAKE-PARSE-1 | none | none |
| SHAKE-PARSE-2 | `pos_of_keeps`, `parse_pos`, `parse_add`, `err_unexpected` | none (bolt's `cli.word_step` is the only one, in bolt) |
| SHAKE-PARSE-3 | `pos_of_rest`, `parse_rest_none`, `parse_rest_one`, `parse_rest_many` | none (bolt's `cli.walk_plain`, in bolt) |
| SHAKE-PARSE-4 | `find_sub_head`, `parse_nested` | none |
| SHAKE-PARSE-5 | `allowed_any`, `allowed_listed`, `allowed_other`, `err_choice` | `allowed_any` (a lemma) |
| SHAKE-PARSE-6 | `parse_default` | none |
| SHAKE-PARSE-7 | `err_missing`, `err_rest_missing` | none |
| SHAKE-PARSE-8 | `err_help_root`, `err_help_greet` | none |
| SHAKE-PARSE-9 | none | none |
| SHAKE-PARSE-10 | none | none |
| SHAKE-SPEC-1 | `rest_last_mid` | none |
| SHAKE-GET-1 | `get_nil`, `get_head`, `get_all_two`, `on_nil`, `on_true` | `get_nil`, `on_nil` (lemmas) |
| SHAKE-HELP-1 | none | none |
| SHAKE-HELP-2 | `help_root`, `help_greet`, `help_add`, `help_rest`, `help_rest_req` | none |
| SHAKE-ERR-1 | `err_text_help`, `err_text_unknown` | `err_text_help` (half of the row) |
| SHAKE-ARGS-1 | `copy_nil`, `copy_one` | `copy_one` (one step) |

## Requirements against code

The draft requirements come from the README and the header comment of `shake/main.bend`, since shake has no other statement of what it does. "Confirmed" means we ran the demo binary built from this tree; "by reading" means we read the code and did not run it.

| Requirement | Verdict | Evidence |
| :---- | :---- | :---- |
| README: "`parse` binds flags, options, positionals, and nested commands" | holds | `main.bend:751-851`. Confirmed with `greet --name Ada -v`, `add 2 3 --times 2`, `add 2 3 more` (fixture). |
| README and `main.bend:4`: "A `--` ends option parsing: every word after it is a positional" | holds for `parse`; fails for the program a user runs | `parse.step.raw` (`main.bend:714-722`) does what the README says. The compiled runtime of bend 2.0.26 consumes the first `--` itself and passes the words after it unexamined, so `parse` never sees it. Confirmed: `demo greet -- --name` fails with "the following required argument was not provided: name", while LAWS.bend's `parse_dash` proves `who=--name` for the same words. `demo greet -- -- --name` prints `hello --name`. See finding F1. |
| README: "the runtime also strips `--threads`, `--gpu`, and `--gpu-build`" | partly | `--threads` and `--gpu` are stripped together with the word after them, and the runtime exits 1 when that word is not a count or `on`, `off` or a size. `--gpu-build` is not stripped: the runtime runs the GPU build step and exits 0 without running `main`. Confirmed: `demo greet --gpu-build` prints nothing, exit 0; `demo greet --threads x` prints `bend: expected a thread count of 1 or more after --threads`, exit 1. |
| README: "`--help` is consumed by the Bend runtime of a compiled binary and never reaches the program" | holds, before the first `--` | Confirmed: `demo greet --help` prints the runtime's usage. After a `--` it reaches `parse`: `demo greet -- --help` reports an unknown `--help`. |
| README: "A rest positional keeps every leftover word under one name; `get_all` reads that list" | holds | `parse.take_pos.keep` (`main.bend:563-568`) keeps a rest positional in the pending list; `get_all.bind` (`main.bend:405-410`) collects in bind order, and `parse.finish.miss` reverses binds into argv order. By reading. |
| README: "`get` still reads one value" | holds; which value is unstated | `get.bind` returns the first bind by that name after the reverse, so the first given wins. Confirmed: `demo greet --name Ada --name Bob` prints `hello Ada`. See F3. |
| README: "Print usage with `tool help` or `tool help <command>`" | holds, with an accident | `parse.step.help` (`main.bend:693-700`). An unknown name in the path is skipped: `demo help nope` prints the root page and exits 0; `demo help nope greet` prints `greet`'s page. Confirmed. See F5. |
| `main.bend:2`: "`help` writes usage for a command path" | holds | `help.go` (`main.bend:1098-1105`). |
| `main.bend:145`: "`-` alone is not" a flag token | holds | Confirmed: `demo greet -` binds `who=-`. |
| `main.bend:330`: rest positionals are last and at most one | fails: nothing checks it | `rest.last` (`main.bend:323-328`) is called by no code, only by three closed laws. A spec with a rest positional before a plain one parses: the rest swallows every word and the later positional is never bound. By reading. See F6. |
| bolt's BOLT-TRUST-8: "shake v0.1.1 parses argv as its spec says" | as trusted, with nothing to trust | shake has no spec. See F12. |

## What each entry point reads

shake is a library. Its one IO entry point is `argv` in `shake/args.bend`; everything else is a pure function of its arguments, so the World and planner split that ez and bolt needed is already true of `parse`, `help` and `err_text`.

| Entry point | Reads | Source |
| :---- | :---- | :---- |
| `parse(app, argv)` | the Cli and the word list, nothing else | `main.bend:850-851` |
| `help(app, path)` | the Cli and the path | `main.bend:1108-1110` |
| `err_text(app, e)` | the Cli's name, args and subs, and the error | `main.bend:1113-1131` |
| `argv()` | `IO.args()`, which is what the Bend runtime left of the process's argv | `args.bend:15-17` |

What the runtime leaves is decided outside shake, in the C `main` bend 2.0.26 emits (read out of the bend binary with `strings`): it walks `argv[1..]`; on `--` it copies every later word through and stops looking; on `--help` it prints its own usage and exits 0; on `--gpu-build` it builds the GPU image and exits 0; on `--threads` and `--gpu` it consumes the next word as their value and exits 1 if that value is malformed; every other word is passed on. That is SHAKE-TRUST-2.

No decision is made inside IO and no read falls back to a default, so the tracing found no bug of the ez kind. What it found is that the runtime's rules and shake's rules both claim `--`, and the runtime's run first.

## Findings

Every finding is recorded, not resolved. The RFC carries a REVIEW item for each one a requirement depends on.

### Bugs

- **F1. `--` never reaches `parse` in a compiled binary.** Confirmed. The README, `main.bend:4`, `parse_dash` and `parse_rest_dash` all describe `--` as shake's end of options, and in a compiled binary the runtime takes the first `--` for itself. A user who types `tool add -- -5 3` to pass a negative number gets "unexpected argument '-5'"; they must type `tool add -- -- -5 3`. The code is right about the words it is given; the documentation and the laws describe words no user can give with one `--`.
- **F2. The README build fails on a fresh clone.** Confirmed: `bend examples/demo/main.bend -o bin/demo.bin` fails with "cannot open output file bin/demo.bin" because `bin/` is not tracked. This is the bug ez's README had.
- **F3. The gate does not protect parsing.** Confirmed by the planted truncation bug above: every closed law passes on a parser that drops the seventh character of every value.

### Behavior that looks accidental

- **F4. A repeated option keeps its first value.** Confirmed: `greet --name Ada --name Bob` prints `hello Ada`. `get_all` returns both. clap 4 refuses a repeated single-valued option; getopt-style tools usually keep the last.
- **F5. `help` skips unknown names.** Confirmed: `help nope` prints the root page and exits 0. clap reports an unrecognized subcommand.
- **F6. No spec is ever checked.** By reading. `rest.last` is dead code. Nothing refuses two arguments with one spelling or one name (the first wins at lookup), a subcommand named `help` (it can never be selected), a default outside its own choices (it is bound without the choices test), or a required positional after an optional one.
- **F7. `-n=Ada` binds `=Ada`.** Confirmed. clap binds `Ada` for `-n=Ada`.
- **F8. Error text always shows the root usage line.** Confirmed: an unknown flag inside `greet` shows `Usage: demo [OPTIONS] [COMMAND]`. `err_text` has no path to show another.
- **F9. A missing option value and a missing required argument are one error.** Confirmed: `greet --name` reports "the following required argument was not provided: name". Both are `Missing{name}`.
- **F10. An empty value and no value read the same.** By reading: `get` returns `""` for an unbound name and for `--name=`. `on` is `get == "true"`, so an option given the value `true` is also on.
- **F11. A subcommand name always selects the subcommand.** By reading and confirmed on the fixture: before `--`, a word equal to a subcommand's name is never a positional value. clap does the same by default. We list it because a row needs to say so.

### Behavior no requirement mentions, and other programs

- **F12. bolt depends on shake's internals, and trusts a spec that does not exist.** bolt v1.6.2 pins shake v0.1.1 (`cb02b47`, whose `shake/` tree matches this one), lists it as BOLT-TRUST-8, and proves its own CLI laws by unfolding eight walker defs (`Shake.parse.step`, `Shake.parse.step.end`, `Shake.parse.step.help`, `Shake.parse.step.kind.go`, `Shake.parse.word.go`, `Shake.parse.take_pos`, `Shake.parse.walk`, `Shake.parse.finish`), two accessor helpers (`Shake.get.bind`, `Shake.get_all.bind`), and the walker's `St` and `Mode` types (`bolt/PROOF.bend`, `cli.word_step` and `cli.walk_plain`). Any rename or restructuring of shake's walker breaks bolt's proofs the day bolt bumps its pin, and nothing in shake says which names are its interface. ez uses only the public surface (`app`, `sub`, `flag`, `opt`, `pos`, `parse`, `help`, `err_text`, `get`, `on`, `path_of`).
- **F13. The pinned bolt cannot enforce the model.** shake pins bolt v0.4.0, which has no `trace` rule; v1.6.2 has `trace`, but its `closed` rule accepts `for u: Unit` just as v0.4.0 does.

### Requirements with no code

- The README says a rest positional is "every leftover word", and nothing checks that the rest is the last positional (F6).

## Rollout progress

| Phase | State | What landed |
| :---- | :---- | :---- |
| Preliminary | done | This inventory and the RFC; the RFC accepted with every review item resolved; the README builds from a fresh clone (`mkdir -p bin`) and, with `main.bend` and `src/cli.bend`, says what a compiled program's runtime takes before shake (F1, F2). |
| Zero | done | The code moved to `src/` behind `main.bend`; ez at `df6d616`; bolt at `ada294e` as a `[tools.bolt]` pin in the lock; the newer style rules' findings fixed; `coverage` at warn, IO marked `# noqa: L001`. |
| One | done | SPEC.md; 73 laws and `src/sample.bend` deleted (every closed law, and every quantified law marked definitional, wiring or wording above); `err_text_help` restated over `main.bend` and tagged SHAKE-ERR-1 as a partial law; `looks_flag_long`, `allowed_any`, `get_nil`, `on_nil` and `copy_one` kept untagged as lemmas; `trace` at error. `coverage` now reports 41 defs no quantified law reaches, the map of what the rows below must reach. |
| Two | done (PARSE-5, TOK-3, TOK-5 and TOK-7 moved to phase three, since each needs a walker step law) | SHAKE-ERR-1 proved (`err_text_iff`, with `err_text_help`). The last-value change for `get` (REVIEW-4) landed on its own, then SHAKE-GET-1 proved by seven laws over `main.bend`, with `hit_append`, `bind_values_append` and `last_snoc` as untagged lemmas and `src/eq.bend` (string equality is reflexive, from ez's `check/eq.bend`); `get_last` is also a partial law of SHAKE-PARSE-10. Each new proof fails when replaced by `{==}`, and `get_last` fails against the old first-value `get`. SHAKE-ARGS-1 proved by `copy_keeps` (the copy read back is the list; it fails against a `copy` that drops words), which replaces the `copy_one` lemma; `argv`'s IO wiring became SHAKE-TRUST-4. SHAKE-PARSE-9 proved by `fail_stays` (frame law, over `parse` with the walker's failure as premise; lemmas `walk_append`, `dead_walk`, `fail_from`); it fails against a walker that recovers after an error. The `help` change (REVIEW-6) landed on its own: `parse` refuses a word after `help` that is not a subcommand where it stands (SHAKE-PARSE-8 stays pending until its law lands). `check` (REVIEW-7) landed on its own: `src/check.bend`, exported from `main.bend` with `SpecErr` and `spec_err_text`, not called by `parse`; `rest.last` deleted (F6). SHAKE-SPEC-1 stays pending until its count and frame laws land. Every decided behavior change has now landed. |
| Three | in progress | The design, [shake-walker-proofs.md](shake-walker-proofs.md), with its spike: bolt's 18 walker lemmas check against today's walker unchanged. WP0 started: `src/walk.bend`, general over any rest positional. WP1 started: SHAKE-TOK-7's refusals, `unknown_long` and `unknown_short`, over `parse` from any walker state reached by the words before (REVIEW-W1's premise form), through step lemmas and `fail_stays`; lemmas `prefix_empty`, `drop_zero`. Each fails as `{==}`, and against a walker that skips an unknown option. The design changes of REVIEW-4, 5 and 11 to 14 landed one PR each, then WP1's refusals on the new shapes, all through the general `refused` lemma: `long_no_name` (TOK-1), `flag_long_valued` (TOK-5, with the not-yet-given premise REVIEW-4 needs), `value_flag_shaped` and `value_absent` (TOK-6, now `NoValue`), `no_pos_left` (PARSE-2), `choice_refused` (PARSE-5), `help_unknown` (PARSE-8), and `repeated_long_flag` and `repeated_long_opt` (PARSE-10, through `once_dead`). Each is caught by a walker mutant that accepts what it refuses. WP2 started: `binds_grow` in `src/grow.bend` (a walker only ever puts bindings in front of those it holds, one lemma per arm of `step`, shaped like bolt's `extends`) and `kept_all` and `kept`, the binding counterparts of `refused`: a binding a step makes is read back by `get_all` of the successful parse, after the values bound before it. Through them: `value_binds` (TOK-6, now proved), `pos_next` and `pos_binds` (PARSE-2), `dd_step`, `raw_next`, `raw_binds`, `raw_no_pos` and `raw_refused` (TOK-4, now proved), `long_binds` (TOK-1, and PARSE-10's `many` half for long spellings), and `value_refused` and `long_refused` (PARSE-5). Stating PARSE-5 found a bug, fixed first: an option's value was checked against a parent's argument of the same name. Walker mutants that drop or replace bindings, bind the name for the value, keep `--` from switching to positionals, or refuse a repeated `many` option each fail the gate. REVIEW-16 then made bindings per command: `binds_grow` became `gw.reach` (a word stays in the current command, putting bindings in front, or enters a subcommand, which keeps the command it leaves above it, or leaves the walker stuck in help or failed), and `kept_all` and `kept` now conclude over `get_all` of the command at the walker's path in the result (`all_at`), through `gw.finished`, `gw.at_build` and the depth invariant `gw.depth`. SHAKE-GET-1 is restated over the new `Matched` and SHAKE-GET-2 proves its navigation. Walker mutants that let a subcommand inherit its parent's bindings, drop a command's bindings from its Matched, build the levels leaf first, forget the parent on entering, or let `at` ignore names each fail the gate. Then `cut_first_eq` and `cut_no_eq`: the `=` cut of a long option's body splits at its first `=`, the value verbatim, which discharges `long_binds`' cut premise, so SHAKE-TOK-1 is proved; a cut that ignores `=`, or loses a char of the value, fails the gate. SHAKE-PARSE-3 is proved by `rest_next` and `rest_binds` (before `--`) and `rest_raw_next` and `rest_raw_binds` (after it), general over a rest with choices, not only bolt's `files`: each word binds the rest and leaves it pending, and `get_all` of its command's Matched reads the words in order; a walker that consumes a rest like a plain positional fails the gate. SHAKE-PARSE-6 and PARSE-7 are proved per command over the finished walker's frame (`fin.at`: the Matched of the command at a path is its level, defaults filled): `default_filled`, `bound_kept`, `no_default` and `no_argument` for defaults, and `required_present` and `required_missing` for required arguments; a fill that overwrites a bound value, a missing default that binds the empty string, a required check that never fires, or parents left without their defaults each fail the gate. SHAKE-PARSE-4 is proved by `enter_step` (entering a subcommand: its arguments current, its positionals pending, no bindings of its own, the command left above it; also SHAKE-TOK-7's half about the current argument list), `enter_missing`, `none_blocking` and `first_blocking`; the row now says what blocks a subcommand as the code does: a pending positional that is required, has no default and is not a rest. SHAKE-PARSE-8 is proved by `help_step` (`help` starts a help path), `help_walk` (each word naming a subcommand under the one before extends it), `help_path` (the words ending there fail with NeedHelp of the whole path) and WP1's `help_unknown`; a help path that does not grow, or a `help` never recognized, fails the gate. SHAKE-PARSE-2 is proved with `start_state` (the root's positionals pending at the start), `pos_of_app`, `pos_of_pos` and `pos_of_opt` (the pending list is exactly the positional arguments, in spec order), `enter_step` (a subcommand's own on entry), and `help_word_next` and `help_word_binds` (a word `help` once a positional is bound binds like any other); positionals pending out of order, or `help` read as a request after a positional, fail the gate. The short clusters: `short_step` (a word `-...` is read as a cluster from the walker as it stood) and one law per kind of letter over the cluster function, `letter_flag`, `letter_flag_eq`, `letter_flag_again`, `letter_opt_again`, `letter_unknown`, `letter_value`, `letter_value_eq`, `letter_value_next` and `letter_value_bad`, with `cluster_dead` (a letter after a failed one changes nothing, which stating PARSE-10 found broken and was fixed first); and `plain_word_step` and `dash_word_step` for TOK-3. With them SHAKE-TOK-2, TOK-3, TOK-5, TOK-7, PARSE-5 and PARSE-10 are proved, and no pending row has partial laws left. Mutants that keep the `=` of `-n=Ada`, end a cluster at a flag, or drop a char of a glued value fail the gate. SHAKE-HELP-1 is proved by `help_page` (the help text for a path is the page of the command the path reaches), `reach_child` and `reach_skip` (a name found under the current command moves to it, an unknown one stays put), stated over law-side `reach` and `page` helpers in `src/LAWS.bend`; SHAKE-ERR-2 by `err_path_at` (each error names the command path it arose at) and `err_text_usage` (an error's text shows that command's usage line), with the refusal laws tagged too, since each names the path its error carries. An error text that shows the root's usage, or a help walk that loses the subcommands on an unknown name, fails the gate. SHAKE-HELP-2 is proved by `cmds_listed` (a page's Commands block is one line per subcommand, in spec order, then `help`'s), `opts_listed` (its Options block is one line per flag and option, from Base's `List.filter`, in spec order) and `usage_listed` (the usage line names the positionals, filtered the same way, each as a law-side `mark`: `<NAME>` or `[NAME]`, then `...` for a rest); commands out of order, no `help` line, a dropped option line, swapped brackets, a positional named twice, or `...` after every positional each fail the gate. SHAKE-SPEC-1 is proved by `check_listed` (WP6): rather than the counts and frame law the design planned, it states the whole report list, which fixes both at once. `check` of a Cli is its root's reports, then each subcommand's at its own path, depth first; a command's reports are each argument's against the arguments before it (a name or spelling they have, a default outside nonempty choices), then each positional's against those before it (a rest with one after it, a required one after an optional one), then each subcommand's against its earlier siblings (a name they have, the name `help`); all stated in `src/LAWS.bend` over the arguments before, not `check`'s accumulators. A `check` that skips nested commands, gives them reversed paths, compares long spellings with short ones, refuses a default when there are no choices, forgets an optional positional, forgets a subcommand's name, or allows a subcommand named `help` fails the gate. |

The planted truncation bug (F3) is still not caught: no row about values is proved yet. PARSE-1 is the row that catches it.
