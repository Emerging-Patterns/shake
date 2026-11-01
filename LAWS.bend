# shake's laws. Each guarantee is one file under laws/, its prose on top and
# its quantified laws under it, proved by the file of the same name under
# proofs/; LAWS.bend and PROOF.bend only import them. The gate: the first line
# `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. Tests and fixtures
# are never evidence for a guarantee; what shake cannot prove is said where it
# is assumed, on the code.
#
# Every guarantee is about the interface in main.bend: its types, builders,
# `parse`, `parse_env`, `check`, `check_reads`, the readers, `help`,
# `err_text`, `help_path`, `err_path`, `version_of`, `suggestion`, `argv` and
# `env_vars`. Every module under src/ is internal and carries no promise.
#
# A spec is well-formed when `check` reports nothing for it
# (laws/CheckReportsSpecErrors.bend). The parse guarantees hold for
# well-formed specs; a spec that contradicts itself, such as two options
# spelled `-n`, is its author's bug and not an input a user can give. Every
# error a guarantee names but `NeedHelp` and `NeedVersion` also carries `at`,
# the command path selected where the parse failed
# (laws/ErrTextShowsUsage.bend); the guarantees write it only where it
# matters. A plain word is `-`, or a word that does not start with `-`. The
# current command is the command whose arguments `parse` matches words
# against: the root, then each subcommand it selects. The selected path is the
# names of the subcommands selected, in order. A successful parse answers the
# root command's Matched, as clap answers `ArgMatches`: the bindings that
# command made while it was current and, when a subcommand was selected under
# it, that subcommand's name and its own Matched, and so on down the selected
# path.
#
# The words `parse` receives are what the program passes it. In a compiled
# program they come from `argv`, which drops the program name `IO.args` starts
# with, after the runtime has taken its own words: those between `+RTS` and
# `-RTS`, and a `--RTS` (trusted in src/args.bend). A `--` the user types
# reaches `parse`.
#
# An argument's env var is the name `env` gives it; an argument built without
# `env` has none. `parse_env` also receives vars, a list of name and value
# pairs, which in a compiled program come from `env_vars` (trusted in
# src/args.bend). An argument's env value is the value of the first pair in
# vars named by its env var, when that value is not empty; an env var no pair
# names, or whose first pair's value is empty, gives no env value.
#
# The reasoning behind each guarantee is in docs/rfc/shake-spec.md and
# docs/rfc/shake-env-and-suggestions.md, which name them by the requirement
# IDs they had before laws/.
import Base
import ./laws/AllowedAny.bend as AllowedAny
import ./laws/ArgLineMark.bend as ArgLineMark
import ./laws/ArgvDropsProgram.bend as ArgvDropsProgram
import ./laws/BindValuesAppend.bend as BindValuesAppend
import ./laws/BindingsComeFromWords.bend as BindingsComeFromWords
import ./laws/BuiltinsListed.bend as BuiltinsListed
import ./laws/CheckReadsReportsBadReads.bend as CheckReadsReportsBadReads
import ./laws/CheckReportsSpecErrors.bend as CheckReportsSpecErrors
import ./laws/ChoiceRefused.bend as ChoiceRefused
import ./laws/ClusterDead.bend as ClusterDead
import ./laws/ClusterDone.bend as ClusterDone
import ./laws/DeadWalk.bend as DeadWalk
import ./laws/DefaultsFillUnbound.bend as DefaultsFillUnbound
import ./laws/DoubleDashEndsOptions.bend as DoubleDashEndsOptions
import ./laws/DropZero.bend as DropZero
import ./laws/EnterMissing.bend as EnterMissing
import ./laws/EnterStep.bend as EnterStep
import ./laws/EnvFallsBetweenWordsAndDefault.bend as EnvFallsBetweenWordsAndDefault
import ./laws/EnvValueOutsideChoicesFails.bend as EnvValueOutsideChoicesFails
import ./laws/EnvVarsAskedInOrder.bend as EnvVarsAskedInOrder
import ./laws/ErrTextEmptyForRequests.bend as ErrTextEmptyForRequests
import ./laws/ErrTextNamesArgumentForm.bend as ErrTextNamesArgumentForm
import ./laws/ErrTextShowsSuggestion.bend as ErrTextShowsSuggestion
import ./laws/ErrTextShowsUsage.bend as ErrTextShowsUsage
import ./laws/FailFrom.bend as FailFrom
import ./laws/FailureIsFinal.bend as FailureIsFinal
import ./laws/FlagLongValued.bend as FlagLongValued
import ./laws/GetNil.bend as GetNil
import ./laws/GetReadsOwnBindings.bend as GetReadsOwnBindings
import ./laws/HelpFollowsPath.bend as HelpFollowsPath
import ./laws/HelpListsEveryArgument.bend as HelpListsEveryArgument
import ./laws/HelpPage.bend as HelpPage
import ./laws/HelpShowsEnvVar.bend as HelpShowsEnvVar
import ./laws/HelpUnknown.bend as HelpUnknown
import ./laws/HelpWalk.bend as HelpWalk
import ./laws/HelpWordAsksForHelp.bend as HelpWordAsksForHelp
import ./laws/HitAppend.bend as HitAppend
import ./laws/Kept.bend as Kept
import ./laws/KeptAll.bend as KeptAll
import ./laws/KeptSet.bend as KeptSet
import ./laws/KeptUnset.bend as KeptUnset
import ./laws/LastSnoc.bend as LastSnoc
import ./laws/LetterFlagAgain.bend as LetterFlagAgain
import ./laws/LetterFlagEq.bend as LetterFlagEq
import ./laws/LetterOptAgain.bend as LetterOptAgain
import ./laws/LetterUnknown.bend as LetterUnknown
import ./laws/LetterValue.bend as LetterValue
import ./laws/LetterValueBad.bend as LetterValueBad
import ./laws/LetterValueEq.bend as LetterValueEq
import ./laws/LongArgStep.bend as LongArgStep
import ./laws/LongBinds.bend as LongBinds
import ./laws/LongNoName.bend as LongNoName
import ./laws/LongOptionSplitsAtEquals.bend as LongOptionSplitsAtEquals
import ./laws/LongRefused.bend as LongRefused
import ./laws/LooksFlagLong.bend as LooksFlagLong
import ./laws/NoPosLeft.bend as NoPosLeft
import ./laws/OnNil.bend as OnNil
import ./laws/OnceDead.bend as OnceDead
import ./laws/PlainWordIsNeverOption.bend as PlainWordIsNeverOption
import ./laws/PosBinds.bend as PosBinds
import ./laws/PosNext.bend as PosNext
import ./laws/PositionalsBindInOrder.bend as PositionalsBindInOrder
import ./laws/PrefixEmpty.bend as PrefixEmpty
import ./laws/RawBinds.bend as RawBinds
import ./laws/RawNext.bend as RawNext
import ./laws/RawNoPos.bend as RawNoPos
import ./laws/RawRefused.bend as RawRefused
import ./laws/Refused.bend as Refused
import ./laws/RepeatedLongFlag.bend as RepeatedLongFlag
import ./laws/RepeatedLongOpt.bend as RepeatedLongOpt
import ./laws/RequiredMissing.bend as RequiredMissing
import ./laws/RequiredMustBind.bend as RequiredMustBind
import ./laws/RestTakesRemainingWords.bend as RestTakesRemainingWords
import ./laws/ShortClusterReadsLetters.bend as ShortClusterReadsLetters
import ./laws/SpecErrWhere.bend as SpecErrWhere
import ./laws/StepDies.bend as StepDies
import ./laws/SubcommandResultsNavigate.bend as SubcommandResultsNavigate
import ./laws/SubcommandSelects.bend as SubcommandSelects
import ./laws/SuggestionPicksClosestLong.bend as SuggestionPicksClosestLong
import ./laws/UnknownLong.bend as UnknownLong
import ./laws/UnknownLongDies.bend as UnknownLongDies
import ./laws/UnknownLongStep.bend as UnknownLongStep
import ./laws/UnknownShort.bend as UnknownShort
import ./laws/UnknownShortStep.bend as UnknownShortStep
import ./laws/ValueAbsent.bend as ValueAbsent
import ./laws/ValueBinds.bend as ValueBinds
import ./laws/ValueFlagShaped.bend as ValueFlagShaped
import ./laws/ValueRefused.bend as ValueRefused
import ./laws/VersionOfNamesRelease.bend as VersionOfNamesRelease
import ./laws/VersionWordAsksForVersion.bend as VersionWordAsksForVersion
import ./laws/WalkAppend.bend as WalkAppend
