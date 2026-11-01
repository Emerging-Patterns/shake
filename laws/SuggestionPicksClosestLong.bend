# `suggestion(spec, err)` is `None` for every error but an `UnknownFlag{at,
# word}` whose word starts with `--` (laws/LongOptionSplitsAtEquals.bend,
# laws/UnknownSpellingRefused.bend). For such a word, let `typed` be its chars
# after `--` up to its first `=`, and the **candidates** the long spellings of
# the flags and options of the command at `at`, reached as `help(spec, at)`
# reaches it (laws/HelpFollowsPath.bend), in spec order; a parent command's
# arguments, subcommands and `help` are not candidates. A candidate `c` is
# **close** when `0 < d` and `3 * d <= max(length(typed), length(c))`, where
# `d` is the optimal string alignment distance from `typed` to `c`: the fewest
# single-char insertions, deletions, substitutions and swaps of two adjacent
# chars that turn one into the other, editing no char twice. The suggestion is
# `Some{"--" ++ c}` for the close candidate with the least `d`, the first in
# spec order among equals, and `None` when no candidate is close. A short
# option word never gets one.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/HelpPages.bend as D1

# the arguments of a page's command
def how_args(how: S.How) -> List<&2, S.Arg>:
  S.How{_b, _a, _v, args, _s, _u} = how
  args

# LAW: only an unknown option can get a suggestion
law sug_other:
  for spec: Shake.Cli
  for +err: Shake.ParseErr
  for h_err: {D1.unknown.is(err) == False{} : Bool}
  {Shake.suggestion(spec, err) == None{} : Maybe<&2, String>}

# LAW: a word that does not start with `--` gets no suggestion
law sug_short:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +word: String
  for h_word: {String.starts_with(word, "--") == False{} : Bool}
  {Shake.suggestion(spec, S.UnknownFlag{at, word}) == None{} : Maybe<&2, String>}

# LAW: a long option word's suggestion is the closest close candidate to its
# spelling up to `=`, among the long spellings of the command at `at`, reached
# as `help` reaches it, as a long option word
law sug_long:
  for +spec: Shake.Cli
  for +at: List<&2, String>
  for +body: String
  for +name: String
  for val: Maybe<&2, String>
  for h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>}
  {Shake.suggestion(spec, S.UnknownFlag{at, "--" ++ body})
    == S.sug.found(S.sug.best(S.sug.cands(how_args(D1.reach(at, D1.root(spec)))), name)) : Maybe<&2, String>}

# LAW: a candidate is suggested as its long option word
law sug_found_some:
  for cc: String
  {S.sug.found(Some{cc}) == Some{"--" ++ cc} : Maybe<&2, String>}

# LAW: an argument with a long spelling is a candidate, in spec order
law cands_some:
  for nn: String
  for sh: Maybe<&2, String>
  for ll: String
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for fb: S.Fallback
  for cs: List<&2, String>
  for tt: List<&2, S.Arg>
  {S.sug.cands(S.Arg{nn, sh, Some{ll}, kind, hp, req, fb, cs} <> tt) == ll <> S.sug.cands(tt) : List<&2, String>}

# LAW: an argument with no long spelling is not a candidate
law cands_none:
  for nn: String
  for sh: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for fb: S.Fallback
  for cs: List<&2, String>
  for tt: List<&2, S.Arg>
  {S.sug.cands(S.Arg{nn, sh, None{}, kind, hp, req, fb, cs} <> tt) == S.sug.cands(tt) : List<&2, String>}

# LAW: a candidate is close when it is some edits away, and three times as
# many is at most the longer length
law sug_close:
  for +typed: String
  for +cc: String
  {S.sug.close(typed, cc)
    == Bool.and(Nat.is_lt(0n, S.osa(typed, cc)),
      Nat.is_le(Nat.mul(3n, S.osa(typed, cc)), Nat.max(String.length(typed), String.length(cc)))) : Bool}

# LAW: no candidates, no closest one
law best_nil:
  for typed: String
  {S.sug.best([], typed) == None{} : Maybe<&2, String>}

# LAW: a candidate that is not close is passed over
law best_far:
  for +cc: String
  for +tt: List<&2, String>
  for +typed: String
  for h_far: {S.sug.close(typed, cc) == False{} : Bool}
  {S.sug.best(cc <> tt, typed) == S.sug.best(tt, typed) : Maybe<&2, String>}

# LAW: a close candidate with none close after it is the closest
law best_only:
  for +cc: String
  for +tt: List<&2, String>
  for +typed: String
  for h_close: {S.sug.close(typed, cc) == True{} : Bool}
  for h_rest: {S.sug.best(tt, typed) == None{} : Maybe<&2, String>}
  {S.sug.best(cc <> tt, typed) == Some{cc} : Maybe<&2, String>}

# LAW: a close candidate no farther than the closest after it is the closest:
# the first wins a tie
law best_here:
  for +cc: String
  for +tt: List<&2, String>
  for +typed: String
  for +ww: String
  for h_close: {S.sug.close(typed, cc) == True{} : Bool}
  for h_rest: {S.sug.best(tt, typed) == Some{ww} : Maybe<&2, String>}
  for h_le: {Nat.is_le(S.osa(typed, cc), S.osa(typed, ww)) == True{} : Bool}
  {S.sug.best(cc <> tt, typed) == Some{cc} : Maybe<&2, String>}

# LAW: a close candidate farther than the closest after it is passed over
law best_there:
  for +cc: String
  for +tt: List<&2, String>
  for +typed: String
  for +ww: String
  for h_close: {S.sug.close(typed, cc) == True{} : Bool}
  for h_rest: {S.sug.best(tt, typed) == Some{ww} : Maybe<&2, String>}
  for h_le: {Nat.is_le(S.osa(typed, cc), S.osa(typed, ww)) == False{} : Bool}
  {S.sug.best(cc <> tt, typed) == Some{ww} : Maybe<&2, String>}
