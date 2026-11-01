# A long or short spelling that no argument of the current command has is
# refused as `UnknownFlag{word}`, except a word `--help` or `-h` that
# laws/HelpWordAsksForHelp.bend reads as a request for help, and a word `--version` or `-V`
# that laws/VersionWordAsksForVersion.bend reads as a request for the version. Arguments of a parent
# command are not matched after a subcommand is selected.
#
# also rests on: laws/EnterStep.bend, laws/LetterUnknown.bend,
# laws/UnknownLong.bend, laws/UnknownShort.bend
import Base


