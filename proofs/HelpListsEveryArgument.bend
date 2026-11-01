# proofs of laws/HelpListsEveryArgument.bend
import Base
import ../src/cli.bend as S
import ../laws/HelpListsEveryArgument.bend as Laws
import ./lemmas/StringAppendEmpty.bend as M1

# the Commands lines are the subcommands' lines, then `help`'s
def hs.cmds(
  +subs: List<&2, S.Sub>,
  +ww: Nat
) -> {S.help.cmd_lines(subs, ww) == Laws.sub_lines(List.append(&2, S.Sub, subs, [Laws.help_sub()]), ww) : String}:
  match subs:
    case Nil{}:
      Equal.sym(String, S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww) ++ "",
        S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww),
        M1.hs.nil(S.help.cmd_line("help", "Print this message or the help of the given subcommand(s)", ww)))
    case Con{+hh, +tt}:
      Equal.cong(String, String, xs => S.help.cmd_line(S.help.sub_name(hh), S.help.sub_about(hh), ww) ++ xs,
        S.help.cmd_lines(tt, ww), Laws.sub_lines(List.append(&2, S.Sub, tt, [Laws.help_sub()]), ww), hs.cmds(tt, ww))

def Laws.cmds_listed(subs):
  Equal.cong(String, String, xs => "Commands:\n" ++ xs ++ "\n", S.help.cmd_lines(subs, S.help.cmd_width(subs, 0n)),
    Laws.sub_lines(List.append(&2, S.Sub, subs, [Laws.help_sub()]), S.help.cmd_width(subs, 0n)),
    hs.cmds(subs, S.help.cmd_width(subs, 0n)))

# an option's line, then the lines after it
def hs.opt_next(
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +ww: Nat,
  ee: {S.help.opt_lines(tt, ww) == Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww) : String}
) -> {S.help.opt_line(aa, ww) ++ "\n" ++ S.help.opt_lines(tt, ww)
    == S.help.opt_line(aa, ww) ++ "\n" ++ Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww) : String}:
  Equal.cong(String, String, xs => S.help.opt_line(aa, ww) ++ "\n" ++ xs, S.help.opt_lines(tt, ww),
    Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, tt), ww), ee)

# the Options lines are the lines of the flags and options, in order
def hs.opts(
  +args: List<&2, S.Arg>,
  +ww: Nat
) -> {S.help.opt_lines(args, ww) == Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, args), ww) : String}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, kind, +h, +r, +d, +c}:
          match kind:
            case S.Flag{}:
              hs.opt_next(S.Arg{n, s, l, S.Flag{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Opt{}:
              hs.opt_next(S.Arg{n, s, l, S.Opt{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Many{}:
              hs.opt_next(S.Arg{n, s, l, S.Many{}, h, r, d, c}, tt, ww, hs.opts(tt, ww))
            case S.Pos{}:
              hs.opts(tt, ww)
            case S.Rest{}:
              hs.opts(tt, ww)

def Laws.opts_listed(args):
  Equal.cong(String, String, xs => S.help.opts.go(xs), S.help.opt_lines(args, S.help.opt_width(args, 0n)),
    Laws.opt_lines(List.filter(~S.Arg, ~Laws.is_opt, args), S.help.opt_width(args, 0n)),
    hs.opts(args, S.help.opt_width(args, 0n)))

# a positional's hint, then the hints after it
def hs.pos_next(
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  ee: {S.help.pos(tt) == Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt)) : String}
) -> {S.help.pos.one(aa) ++ S.help.pos(tt) == S.help.pos.one(aa) ++ Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt))
    : String}:
  Equal.cong(String, String, xs => S.help.pos.one(aa) ++ xs, S.help.pos(tt),
    Laws.marks(List.filter(~S.Arg, ~S.pos.is, tt)), ee)

# the usage hints are the marks of the positionals, in order
def hs.pos(+args: List<&2, S.Arg>) -> {S.help.pos(args) == Laws.marks(List.filter(~S.Arg, ~S.pos.is, args)) : String}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, kind, +h, r, +d, +c}:
          match kind:
            case S.Flag{}:
              hs.pos(tt)
            case S.Opt{}:
              hs.pos(tt)
            case S.Many{}:
              hs.pos(tt)
            case S.Pos{}:
              match r:
                case True{}:
                  hs.pos_next(S.Arg{n, s, l, S.Pos{}, h, True{}, d, c}, tt, hs.pos(tt))
                case False{}:
                  hs.pos_next(S.Arg{n, s, l, S.Pos{}, h, False{}, d, c}, tt, hs.pos(tt))
            case S.Rest{}:
              match r:
                case True{}:
                  hs.pos_next(S.Arg{n, s, l, S.Rest{}, h, True{}, d, c}, tt, hs.pos(tt))
                case False{}:
                  hs.pos_next(S.Arg{n, s, l, S.Rest{}, h, False{}, d, c}, tt, hs.pos(tt))

def Laws.usage_listed(name, args, subs):
  Equal.cong(String, String, xs => "Usage: " ++ name ++ S.help.opts_hint(args) ++ xs ++ S.help.cmd_hint(subs),
    S.help.pos(args), Laws.marks(List.filter(~S.Arg, ~S.pos.is, args)), hs.pos(args))

# a positional's Arguments line, then the lines after it
def ha.next(
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +ww: Nat,
  ee: {S.help.arg_lines(tt, ww) == Laws.arg_lines(List.filter(~S.Arg, ~S.pos.is, tt), ww) : String}
) -> {S.help.arg_line(aa, ww) ++ "\n" ++ S.help.arg_lines(tt, ww)
    == S.help.arg_line(aa, ww) ++ "\n" ++ Laws.arg_lines(List.filter(~S.Arg, ~S.pos.is, tt), ww) : String}:
  Equal.cong(String, String, xs => S.help.arg_line(aa, ww) ++ "\n" ++ xs, S.help.arg_lines(tt, ww),
    Laws.arg_lines(List.filter(~S.Arg, ~S.pos.is, tt), ww), ee)

# the Arguments lines are the lines of the positionals, in order
def ha.lines(
  +args: List<&2, S.Arg>,
  +ww: Nat
) -> {S.help.arg_lines(args, ww) == Laws.arg_lines(List.filter(~S.Arg, ~S.pos.is, args), ww) : String}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, kind, +h, +r, +d, +c}:
          match kind:
            case S.Flag{}:
              ha.lines(tt, ww)
            case S.Opt{}:
              ha.lines(tt, ww)
            case S.Many{}:
              ha.lines(tt, ww)
            case S.Pos{}:
              ha.next(S.Arg{n, s, l, S.Pos{}, h, r, d, c}, tt, ww, ha.lines(tt, ww))
            case S.Rest{}:
              ha.next(S.Arg{n, s, l, S.Rest{}, h, r, d, c}, tt, ww, ha.lines(tt, ww))

def Laws.args_listed(args):
  Equal.cong(String, String, xs => S.help.args.go(xs), S.help.arg_lines(args, S.help.arg_width(S.pos_of(args), 0n)),
    Laws.arg_lines(List.filter(~S.Arg, ~S.pos.is, args), S.help.arg_width(S.pos_of(args), 0n)),
    ha.lines(args, S.help.arg_width(S.pos_of(args), 0n)))
