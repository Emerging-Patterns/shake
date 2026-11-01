# For every error but a request for help or for the version, `err_path(err)`
# is the path of subcommands the parse had selected at the word that failed
# it, and `err_text(spec, err)` shows the usage line of the command at that
# path, as `help(spec, err_path(err))` does. `err_path(NeedVersion{})` is
# `[]`.
#
# also rests on: laws/ChoiceRefused.bend, laws/EnterMissing.bend,
# laws/FlagLongValued.bend, laws/HelpPage.bend, laws/HelpUnknown.bend,
# laws/LetterFlagAgain.bend, laws/LetterFlagEq.bend, laws/LetterOptAgain.bend,
# laws/LetterUnknown.bend, laws/LetterValueBad.bend, laws/LongNoName.bend,
# laws/LongRefused.bend, laws/NoPosLeft.bend, laws/RawNoPos.bend,
# laws/RawRefused.bend, laws/RepeatedLongFlag.bend, laws/RepeatedLongOpt.bend,
# laws/RequiredMissing.bend, laws/UnknownLong.bend, laws/UnknownShort.bend,
# laws/ValueAbsent.bend, laws/ValueFlagShaped.bend, laws/ValueRefused.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/HelpPages.bend as D1
import ./defs/VersionRequest.bend as D2

# LAW: every error but a request for help names the command path where the
# parse failed, and `err_path` reads it; a request for the version names the
# root
law err_path_at:
  for +at: List<&2, String>
  for +word: String
  for +name: String
  for +value: String
  {[Shake.err_path(S.UnknownFlag{at, word}), Shake.err_path(S.Missing{at, name}), Shake.err_path(S.NoValue{at, name}),
      Shake.err_path(S.BadValue{at, name, value}), Shake.err_path(S.Unexpected{at, word}),
      Shake.err_path(S.Repeated{at, name}), Shake.err_path(S.NeedVersion{})]
    == [at, at, at, at, at, at, []] : List<&2, List<&2, String>>}

# LAW: the text of every error but a request for help or for the version is a
# message, then the usage line of the command at its path, as that command's
# help page shows it, then where to look for more
law err_text_usage:
  for +spec: Shake.Cli
  for +err: Shake.ParseErr
  for h_err: {Shake.help_path(err) == None{} : Maybe<&2, List<&2, String>>}
  for h_ver: {D2.version.is(err) == False{} : Bool}
  exs msg: String
  {Shake.err_text(spec, err)
    == msg ++ "\n\n" ++ D1.usage_line(D1.reach(Shake.err_path(err),
        D1.root(spec))) ++ "\n\n" ++ S.err.hint(Shake.err_path(err))
    : String}
