# When the spec has a version, `parse` fails with `NeedVersion{}` wherever it
# would otherwise fail with `UnknownFlag{[], "--version"}`, and wherever it
# would otherwise fail with `UnknownFlag{[], "-V"}` when no argument of the
# root command has the long spelling `version`: that is, when the first word
# to fail the parse is `--version` or `-V` read while the root command is
# current (laws/FailureIsFinal.bend, laws/UnknownSpellingRefused.bend). Every
# other result of the parse is what it would be without this row, and
# `parse_env` reads the version as `parse` does
# (laws/EnvFallsBetweenWordsAndDefault.bend).
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/HelpPages.bend as D1

# whether a word refused at `at` asks for the version: `--version`, or `-V`
# when the root does not spell `--version`, refused at the root of a spec
# with a version
def asks_version(spec: Shake.Cli, +at: List<&2, String>, +word: String) -> Bool:
  S.Cli{_n, _a, version, args, _s} = spec
  Bool.and(Bool.or(String.eq(word, "--version"),
      Bool.and(String.eq(word, "-V"), Maybe.is_none(&2, S.Arg, S.by_long(args, "version")))),
    Bool.and(List.is_empty(&2, String, at), Maybe.is_some(&2, String, version)))

# whether a parse's answer refuses an unknown option
def unknown.res(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> Bool:
  match rr:
    case Done{_m}:
      False{}
    case Fail{ee}:
      D1.unknown.is(ee)

# LAW: where the walk would refuse a word that asks for the version, the
# parse fails with a request for the version
law version_asked:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +at: List<&2, String>
  for +word: String
  for h_walk: {S.parse.finish(S.parse.walk(ws, S.parse.start(spec))) == Fail{S.UnknownFlag{at, word}}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_asks: {asks_version(spec, at, word) == True{} : Bool}
  {Shake.parse(spec, ws) == Fail{S.NeedVersion{}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: where the walk would refuse a word that does not ask for the version,
# the parse refuses it
law version_unasked:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +at: List<&2, String>
  for +word: String
  for h_walk: {S.parse.finish(S.parse.walk(ws, S.parse.start(spec))) == Fail{S.UnknownFlag{at, word}}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_asks: {asks_version(spec, at, word) == False{} : Bool}
  {Shake.parse(spec, ws) == Fail{S.UnknownFlag{at, word}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: every other answer of the walk is the parse's
law version_other:
  for +spec: Shake.Cli
  for +ws: List<&2, String>
  for +rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>
  for h_walk: {S.parse.finish(S.parse.walk(ws, S.parse.start(spec))) == rr
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_rr: {unknown.res(rr) == False{} : Bool}
  {Shake.parse(spec, ws) == rr : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: resolving the env vars keeps the version and every long spelling, so
# `parse_env`'s parse asks for the version where `parse`'s does
law resolve_asks:
  for +spec: Shake.Cli
  for +vars: List<&2, Shake.Var>
  for +at: List<&2, String>
  for +word: String
  {asks_version(S.resolve(spec, vars), at, word) == asks_version(spec, at, word) : Bool}
