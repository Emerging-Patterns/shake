# Design: proving the walker rows

This is the design for phase three of [shake-spec.md](shake-spec.md): the rows whose laws have to follow `parse` word by word. They are SHAKE-TOK-1 to TOK-7, SHAKE-PARSE-1 to PARSE-8 and PARSE-10, SHAKE-SPEC-1 and SHAKE-HELP-1 and HELP-2. It follows the shape of ez's `ez-lock-planner.md`: what exists, the spike, the law patterns, the work packages and their order, and the open questions.

**Update:** WP0's first part landed with this document: `src/walk.bend` holds the spike's lemmas, generalized from bolt's `files` positional to any rest positional with no choices (its name, help, required flag and default are binders), in the gate through `src/PROOF.bend`. bolt's `cli.walk_dead` was dropped, since shake's `dead_walk` states the same. Still to do in WP0: the same for a plain positional list.

## Draft Status

**State:** Accepted

- [x] <!-- REVIEW-W1 (resolved): Laws for the walker rows state their premise about the walker's state, not only about `parse`'s inputs. SHAKE-PARSE-9's `fail_stays` already does: "when walking `ws` leaves the walker failed with `err`". The alternative, a premise over the spec and words alone ("the words before `w` are all plain and name no subcommand"), is much longer to state and to prove, and says less. The rows stay worded over `main.bend`; the laws reach the walker through `src/cli.bend`, as ezjson's laws reach `value.bend`. Recommend: premises over the walker's state. Decision: approved; the WP1 and WP2 laws already take this form. -->
- [x] <!-- REVIEW-W2 (resolved): The walker lemmas bolt proved for its own CLI move into shake (`src/walk.bend`). bolt then deletes its copies and cites SHAKE rows when it bumps shake (WP8). Recommend: yes. Decision: approved. -->

## What exists

`parse(spec, ws)` is `finish(walk(ws, start(spec)))`. `walk` applies `step` to each word in turn. `step` dispatches on the walker's mode (`Free`, `Need`, `Help`, `Dead`) and, in `Free`, on the word's shape: `--`, `help`, a long option, a short option, or a plain word. `finish` turns the last state into `Fail{err}`, or fills defaults, checks required arguments and reverses the bindings into `Done{Matched}`.

Already proved, and reusable here: `walk_append` (walking a concatenation is walking each part in turn), `dead_walk` and `fail_from` (a failed walker stays failed and finishes as its failure), and `fail_stays` (SHAKE-PARSE-9) that puts them together. In `src/LAWS.bend`.

## The spike

The riskiest question was whether the walker, with nine fields threaded through every step, can be reasoned about word by word at a reasonable cost. bolt had already done it against shake v0.1.1 for its own CLI: `cli.word_step` (a plain word in a free walker goes to `take_pos`), `cli.walk_plain` (plain words fill a rest positional in order), `cli.walk_raw` (after `--`, every word does) and 15 supporting lemmas.

The spike copied those 18 laws with their proofs into `src/walk.bend`, changing only the module alias and a name prefix, and checked them against today's walker: `All terms check.` in 0.3 s. The renames of the style cleanup and the three behavior changes since v0.1.1 did not touch the arms they use. So stepping one word costs about one rewrite per dispatch level, as it did in bolt, and no row in this phase looks expensive enough to move to Trusted.

## Law patterns

Every walker row falls into one of three patterns.

**Refusal.** A word that is refused (TOK-1's `--=...`, TOK-5, TOK-6's flag-shaped value, TOK-7, PARSE-2's word with no positional left, PARSE-5's value outside the choices, PARSE-8's unknown name after `help`) is a step law, "in a state like this, `step(w, st)` is failed with `err`", then lifted to `parse` through `fail_stays`. That gives `parse(spec, pre ++ [w] ++ more) == Fail{err}` for every `more`, where `pre` leaves the walker in that state. The lift is free once the step law exists.

**Binding.** A word that binds (TOK-1, TOK-2, TOK-4, TOK-6's accepted half, PARSE-2, PARSE-3, PARSE-5's accepted half) is a step law, "`step(w, st)` is `st` with `Bind{name, value}` in front", plus one invariant: a free walker only ever adds bindings to the front, and `finish` reverses them after the defaults. So a binding made at word *i* is in the `Matched`, in order, unless a later word fails the parse. This invariant is the one new lemma of weight, `binds_grow`.

**Finishing.** PARSE-6 (defaults) and PARSE-7 (required) are about `finish` alone: `fill.args` adds exactly the defaults of unbound names, and `miss.args` finds a required name exactly when it is unbound. These are list lemmas like GET-1's.

PARSE-1, the headline, is an induction over the words with `binds_grow` as the invariant and the binding step laws as its cases. PARSE-4 (entering a subcommand) and PARSE-8 (the help path) are their own step laws.

## Work packages

|  |
|:---:|
| <pre>WP0 walk.bend ──┬──▶ WP1 refusals ───────────────┐<br>                ├──▶ WP2 bindings ──▶ WP8 bolt   ├──▶ WP5 PARSE-1<br>                ├──▶ WP3 finish (PARSE-6, 7) ────┤<br>                └──▶ WP4 enter, help (PARSE-4, 8)┘<br>WP6 check (SPEC-1)      WP7 help pages (HELP-1, 2)</pre> |
| Caption: WP0 first; WP1 to WP4 in any order; WP5 last. WP6 and WP7 depend on nothing here. |

| WP | Scope | Rows | Needs | Effort |
| :---- | :---- | :---- | :---- | :---- |
| WP0 | `src/walk.bend`: the spike's lemmas, generalized from bolt's `files` rest to any positional and any rest | none (lemmas) | nothing | small |
| WP1 | refusal step laws, each lifted with `fail_stays` | TOK-5, TOK-7; the refusal halves of TOK-1, TOK-6, PARSE-2, PARSE-5, PARSE-8 | WP0 | small |
| WP2 | binding step laws and `binds_grow` | TOK-1, TOK-2, TOK-3, TOK-4, TOK-6, PARSE-2, PARSE-3, PARSE-5, PARSE-10's missing half | WP0 | medium |
| WP3 | `fill.args` and `miss.args` lemmas | PARSE-6, PARSE-7 | WP0 | medium |
| WP4 | entering a subcommand, the help path | PARSE-4, PARSE-8 | WP0 | medium |
| WP5 | the headline, by induction over the words | PARSE-1 | WP1 to WP4 | large |
| WP6 | `check` as count equalities and a frame law | SPEC-1 | nothing | medium |
| WP7 | help pages as occurrence counts | HELP-1, HELP-2 | nothing | medium |
| WP8 | bolt cites SHAKE-PARSE-2 and PARSE-3, deletes its `cli.*` walker lemmas, narrows BOLT-TRUST-8 | none in shake | WP2, a shake release | small, in bolt |

Each WP lands as one PR that flips the rows it completes and names what it leaves pending.

## Risks

- **`binds_grow` touches every arm of `step`.** It is the one lemma that cannot be scoped to a word shape. If it is expensive, WP2's rows can still land as "the binding is made by this step" and PARSE-1 waits; nothing else depends on it.
- **The walker changes under the laws.** A tagged law now names walker internals in its premise (REVIEW-W1). A refactor of the walker then has to re-prove, but not restate, the rows: the statements are over `parse`, and only the premises and proofs move.
