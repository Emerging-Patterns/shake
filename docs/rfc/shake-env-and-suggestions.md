# RFC: env-var fallbacks and "did you mean" for unknown flags

Read at `f142895` on `main`, bend 2.0.34, bolt v1.11.0. Requested by the maintainer for bend-kit, as two clap features: `Arg::env` and the `suggestions` feature.

## Draft Status

**State:** Accepted and implemented; every row it adds to SPEC.md is proved (see [Rollout](#rollout)).

- [x] <!-- REVIEW-E1 (resolved): `parse` keeps its signature. Env values reach the parser through a new pure `parse_env(spec, words, vars)`, and the process's variables through a new IO `env_vars(spec)`, beside `argv`. The alternative, a third argument on `parse`, breaks every caller to add something most programs do not use. -->
- [x] <!-- REVIEW-E2 (resolved): an env var set to the empty string gives no env value, as if it were unset, so `NAME= tool` falls back to the default (the shell's `${NAME:-default}`). A word still binds an empty value (`--name=`, SHAKE-TOK-1). clap 4 binds the empty value; we do not follow it, because an empty variable is how a shell user clears one. -->
- [x] <!-- REVIEW-E3 (resolved): env works for flags as clap's `SetTrue` reads it: a flag whose env value, lowercased, is none of `0 false no off n f` is set. A flag whose env value is one of those is not set. -->
- [x] <!-- REVIEW-E4 (resolved): an env value outside its argument's choices fails the parse with `BadValue`, but only when its argument is on the selected path, was left unbound by the words, and the parse would otherwise succeed. Any other error, a request for help included, comes first. -->
- [x] <!-- REVIEW-E5 (resolved): suggestions are for unknown long spellings only, among the current command's flags and options, by optimal string alignment distance (Levenshtein plus adjacent swaps) with `3 * d <= max(length)`. The suggestion is computed from the spec and the error by a new `suggestion(spec, err)`; `ParseErr` does not change. -->

## Problem

shake binds what the words give and fills what they leave with each argument's default (SHAKE-PARSE-6). clap also lets an argument name an environment variable: the words win, then the variable, then the default, and help shows `[env: NAME]`. And when a long option is misspelled clap says which one was meant. bend-kit wants both from shake.

Four things in the existing system shape the answer. `parse` is pure, and every proved row is about it; the only IO is `argv`. Bend 2.0.34 can read one named variable (`IO.get_env`) but cannot list the environment. `Arg` is destructured positionally at about 250 sites in the laws and proofs. And whether a required positional blocks a subcommand is decided while the words are read (SHAKE-PARSE-4, `parse.req`), from the argument's default, so a variable that should stand in for the default has to be known before the walk starts, not only at the end.

## Usage (caller's view)

README:

```bend
import shake@0.5.0.0/main.bend as Shake

def spec() -> Shake.Cli:
  Shake.app("hi", "Say hello.", None{},
    [Shake.env(Shake.opt("name", Some{"n"}, Some{"name"}, "Who to greet", False{},
       Some{"world"}, []), "HI_NAME"),
     Shake.env(Shake.flag("loud", Some{"l"}, Some{"loud"}, "Shout"), "HI_LOUD")],
    [])

def main() -> IO(Unit):
  do IO<Unit>:
    av : List<&2, String> <- Shake.argv()
    ev : List<&2, Shake.Var> <- Shake.env_vars(spec())
    IO.print(greet(Shake.parse_env(spec(), av, ev)))
```

`HI_NAME=Ada hi` prints `hello Ada`, `HI_NAME=Ada hi --name Bo` prints `hello Bo`, and `HI_NAME= hi` prints `hello world`. `hi --help` shows

```
  -n, --name <NAME>  Who to greet [env: HI_NAME] [default: world]
```

and `hi --nmae Ada` fails with

```
error: unexpected argument '--nmae' found

  tip: a similar argument exists: '--name'

Usage: hi [OPTIONS]
...
```

A program that renders its own errors reads the same tip with `Shake.suggestion(spec(), err)`. A pure test passes vars itself: `Shake.parse_env(spec(), [], [("HI_NAME", "Ada")])`.

## Shape

```bend
# src/cli.bend
type Fallback is Data:
  Fallback{env: Maybe<&2, String>, default: Maybe<&2, String>}

type Arg is Data:
  Arg{name, short, long, kind, help, required, fallback: Fallback, choices}

# main.bend, new; a pair `String & String` is a Type, not Data, so a list
# of them is a list of `Var`
def Var() -> Data: Sigma<&2, &2, String, _ => String>
def env(arg: S.Arg, +var: String) -> S.Arg
def parse_env(+spec: S.Cli, words: List<&2, String>, +vars: List<&2, S.Var>)
  -> Result<&2, &2, S.ParseErr, S.Matched>
def suggestion(+spec: S.Cli, err: S.ParseErr) -> Maybe<&2, String>
def env_vars(spec: S.Cli) -> IO(List<&2, S.Var>)
```

**The env var sits beside the default.** `Arg`'s seventh field, the default, becomes `Fallback{env, default}`: both say what an argument falls back to when the words leave it unbound, and keeping them together leaves `Arg` at eight fields, so a destructuring that ignores the default (`_d`) does not change. The builders keep their signatures and build `Fallback{None{}, default}`; `env(arg, var)` sets the env var, as clap's `.env(var)` does, so no caller of a builder breaks.

**`parse_env` resolves fallbacks, then runs the parse that exists.** `parse_env(spec, words, vars)` is `env.check(spec, vars, parse(resolve(spec, vars), words))`. `resolve` rewrites each argument's default to its fallback (SHAKE-PARSE-11); the walker, `finish`, and every proved row about `parse` are unchanged and apply to the resolved spec. This is also why a required positional whose variable is set does not block a subcommand: in the resolved spec it has a default. `env.check` passes every failure through, and turns a success into `BadValue` when an argument on the selected path is bound to an env value outside its choices (SHAKE-PARSE-12). Since a word's value outside the choices never binds (SHAKE-PARSE-5), such a binding can only have come from the variable. `parse(spec, words)` is `parse_env(spec, words, [])`, as a law, not a definition, so existing proofs do not move.

**Policy is pure; IO is one fold.** Empty means unset, the flag literals, and the choices check all live in `resolve` and `env.check`, where laws reach them. `env_vars` asks `IO.get_env` for every env var the spec declares, in every command, since the selected path is not known until the words are read. It keeps the pairs that are set, and passes the values on unchanged (SHAKE-ARGS-2, SHAKE-TRUST-5).

**The suggestion is derived, not stored.** `UnknownFlag{at, word}` already carries what a suggestion needs: `at` reaches the current command, as `err_text` reaches its usage line, and `word` holds the typed spelling. So `ParseErr`, the walker and every refusal law stay as they are. `suggestion` cuts the spelling at `=`, scores it against the long spellings of the flags and options of the command at `at`, and keeps the closest one that is close enough (SHAKE-ERR-3). `err_text` adds clap's tip line when there is one (SHAKE-ERR-4). SHAKE-ERR-1 still holds, because the tip only lengthens a text that was already nonempty.

**Interface depth.** Four new defs. Each hides a policy the caller would otherwise reimplement: `env` hides where the variable is kept, `parse_env` hides precedence, emptiness, flag literals and choices, `env_vars` hides which names to read and in what order, and `suggestion` hides the candidate set, the distance and the threshold. None is a pass-through.

**What it deliberately does not do.** It does not split an env value into several values for `many` or `rest` (one variable is one value). It does not suggest a short letter (`-x` has too little to compare), a parent command's argument, a subcommand for an unexpected word, or `--help`. `--help` is refused only after a positional is bound, so suggesting it there would suggest another refusal. It does not show env values in help, and it does not show a positional's env var, because shake's help has no Arguments block (see [Open questions](#open-questions-and-risks)).

## Synthesis decision

Three candidates were sketched: A (gpt-5.6), C (this author), and B (grok), which returned only after this design was implemented (see the note below). **C is the base:** env applied by rewriting the spec in front of an unchanged `parse`, a post-check for choices, the suggestion derived from the spec and the error, and `parse` kept as it is. **From A:** the `Fallback{env, default}` pair in the default's slot, which C had as a ninth `Arg` field. It cuts the proof churn to the sites that read the default, and it groups two facts that answer one question. Also from A: excluding the synthetic `--help` from the candidates, and a strict first-in-spec-order tie break. **Rejected from A:** a third argument on `parse` (REVIEW-E1); counting an empty variable as set (REVIEW-E2); refusing env on flags in `check` (REVIEW-E3: clap supports it and it fits without changing `on`); a new Arguments block in help (scope beyond the request; an open question); and Jaro similarity. Jaro is clap's measure, but its matching window and transposition count are much harder to state in a row than an edit distance, and the maintainer asked for "edit distance / clap-like". A also checked the fallback against the choices inside `fill`, which changes `finish` and with it the proofs of SHAKE-PARSE-1, PARSE-6 and PARSE-7; C's post-check leaves them untouched.

**B, read after the fact.** B independently reached the same core: `parse` kept as it is, a pure `parse_env` fed by an IO reader, the spec rewritten so a set variable stands in for the default (which unblocks a required positional), a root-first post-check for choices, and the suggestion derived in `err_text` from the spec and `at`. It differs where A did, and the decisions above stand: an empty variable counted as set (REVIEW-E2), no env on flags plus two new `check` errors (REVIEW-E3), Jaro similarity (REVIEW-E5), and a ninth `Arg` field instead of `Fallback`. B also put an env value outside its choices ahead of `Missing`, as clap does. That ordering is already an open question below. B also offered short spellings and a synthetic `--help` as candidates; we keep both out, for the reasons in What it deliberately does not do. Nothing in B changes a SPEC row.

## Tradeoffs accepted

- We accept two parse entry points, `parse` and `parse_env`, in exchange for no breaking change and every existing row applying unchanged.
- We accept `env_vars` reading the variables of commands that end up unselected in exchange for resolving fallbacks before the walk, which is what lets a set variable unblock a required positional.
- We accept that an env value outside its choices is reported only when the parse would otherwise succeed, so a missing argument is reported before a bad variable, in exchange for leaving `finish` and its proofs alone.
- We accept that the distance in SHAKE-ERR-3 is defined by the code that computes it, as every rendering in SHAKE-HELP is. The laws prove which candidate is chosen given the distance, not that the dynamic program matches the textbook recurrence.
- We accept the threshold `3 * d <= max(length(typed), length(c))`, which suggests `--name` for `--nmae` or `--nam` but nothing for a two-letter spelling, in exchange for one integer rule with no floating point.

## Alternatives considered

- **Look up env values in `fill` at the end of the parse** (A's choices check, and the obvious first shape). It is shallow in the wrong place: the walker decides subcommand blocking from defaults before `fill` runs, so a set variable could not unblock a required positional without threading vars through the walker's nine-field state. And the error path inside `fill` rewrites the proofs of three proved rows.
- **A third argument on `parse`.** One entry point instead of two, but every caller in the family breaks to gain a feature most do not use, and `parse(spec, words)` would mean nothing different from `parse(spec, words, [])`.
- **An env parameter on each builder.** It breaks every call of `opt`, `many`, `pos`, `rest` and `flag`, and spreads one optional fact across five signatures.
- **The suggestion as a field of `UnknownFlag`.** It is information `err_text` can derive. Storing it means the walker computes presentation, and every refusal law that names `UnknownFlag` changes.
- **One IO `parse_io(spec)` that reads argv and the environment and parses.** It is the deepest interface for a program, but it hides `argv` and `env_vars` from programs that build words or vars themselves, as tests and bend-kit do. It can be added later on top of these four.

## Open questions and risks

- Should help grow an Arguments block, as clap's has, so a positional's `[env: NAME]` and default can be shown? It changes every help page with positionals and SHAKE-HELP-2's laws, so it is left for its own change.
- Should a missing required argument really be reported before a bad env value? clap reports the bad value first. Changing it means the check moves into `finish` (see Alternatives).
- Proof cost sits in two places: the fold that picks the closest candidate (SHAKE-ERR-3), and `resolve` over the subcommand tree, needed to show `parse_env(spec, words, [])` is `parse(spec, words)`. Both are list inductions of the kind `check_listed` and `values_given` already needed.

## Rollout

| Step | What lands | Rows after |
| :---- | :---- | :---- |
| 1 | this RFC; the rows in SPEC.md as pending | SHAKE-PARSE-11, PARSE-12, HELP-3, ERR-3, ERR-4, ARGS-2 pending; SHAKE-TRUST-5 trusted |
| 2 | `Fallback`, `env`, `parse_env`, `env_vars`, `resolve`, `env.check`, help's `[env: NAME]`; the laws of PARSE-11, PARSE-12, HELP-3, ARGS-2 | those rows proved |
| 3 | `suggestion`, the distance and the tip in `err_text`; the laws of ERR-3, ERR-4 | no pending rows |

## Next implementation step

All three steps have landed and every row is proved. Next, if wanted: an Arguments block in help (see [Open questions](#open-questions-and-risks)).
