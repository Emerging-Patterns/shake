# A page lists each subcommand of its command exactly once, in spec order,
# followed by `help`. When its command has positionals, an Arguments block
# after the subcommands lists each exactly once, in spec order, by the mark
# the usage line gives it without its leading space, then its help text and
# the extras an option line has (laws/HelpShowsEnvVar.bend); a command with no positional
# has no Arguments block. The Options block lists each flag and option exactly
# once, in spec order, followed by the built-in rows of laws/HelpEndsWithBuiltinRows.bend. Its
# usage line names each positional exactly once, in spec order, as `<NAME>`
# when required and `[NAME]` otherwise, with `...` after a rest positional.
#
# also rests on: laws/ArgLineMark.bend, laws/BuiltinsListed.bend
import Base
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1

# the entry every Commands block ends with
def help_sub() -> S.Sub:
  S.Sub{"help", "Print this message or the help of the given subcommand(s)", [], []}

# one Commands line per subcommand, its name and what it is about, in order
def sub_lines(subs: List<&2, S.Sub>, +ww: Nat) -> String:
  match subs:
    case Nil{}:
      ""
    case Con{+hh, tt}:
      S.help.cmd_line(S.help.sub_name(hh), S.help.sub_about(hh), ww) ++ sub_lines(tt, ww)

# LAW: a page's Commands block has one line for each subcommand of its
# command, in spec order, then one for `help`
law cmds_listed:
  for +subs: List<&2, S.Sub>
  {S.help.cmds(subs)
    == "Commands:\n" ++ sub_lines(List.append(&2, S.Sub, subs, [help_sub()]), S.help.cmd_width(subs, 0n)) ++ "\n"
    : String}

# whether an argument is a flag or an option
def is_opt(aa: S.Arg) -> Bool:
  Bool.not(S.pos.is(aa))

# one Options line per argument, in order
def opt_lines(args: List<&2, S.Arg>, +ww: Nat) -> String:
  match args:
    case Nil{}:
      ""
    case Con{+hh, tt}:
      S.help.opt_line(hh, ww) ++ "\n" ++ opt_lines(tt, ww)

# LAW: a page's Options block has one line for each flag and option of its
# command, in spec order, and none for a positional
law opts_listed:
  for +args: List<&2, S.Arg>
  {S.help.opts(args)
    == S.help.opts.go(opt_lines(List.filter(~S.Arg, ~is_opt, args), S.help.opt_width(args, 0n))) : String}

# the marks of a list of positionals, in order
def marks(args: List<&2, S.Arg>) -> String:
  match args:
    case Nil{}:
      ""
    case Con{+hh, tt}:
      D1.mark(hh) ++ marks(tt)

# LAW: a usage line names each positional of its command once, in spec
# order, as `<NAME>` when required and `[NAME]` otherwise, with `...` after a
# rest positional
law usage_listed:
  for +name: String
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  {S.help.usage(name, args, subs)
    == "Usage: " ++ name ++ S.help.opts_hint(args) ++ marks(List.filter(~S.Arg, ~S.pos.is,
        args)) ++ S.help.cmd_hint(subs)
    : String}

# one Arguments line per argument, in order
def arg_lines(args: List<&2, S.Arg>, +ww: Nat) -> String:
  match args:
    case Nil{}:
      ""
    case Con{+hh, tt}:
      S.help.arg_line(hh, ww) ++ "\n" ++ arg_lines(tt, ww)

# LAW: a page's Arguments block has one line for each positional of its
# command, in spec order, and none for a flag or an option; with no
# positional it is empty
law args_listed:
  for +args: List<&2, S.Arg>
  {S.help.args(args)
    == S.help.args.go(arg_lines(List.filter(~S.Arg, ~S.pos.is, args), S.help.arg_width(S.pos_of(args), 0n)))
    : String}
