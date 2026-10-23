# shake/check: the ways a Cli can contradict itself, internal (main.bend
# exports `check`). `parse` does not call it: a program checks its spec once,
# and every guarantee of SPEC.md's parse rows holds for a spec `check` passes.
import Base
import ./cli.bend as C

# one way a spec contradicts itself, at the command path where it does
type SpecErr is Data:
  RestNotLast{path: List<&2, String>, name: String}
  SameName{path: List<&2, String>, name: String}
  SameShort{path: List<&2, String>, short: String}
  SameLong{path: List<&2, String>, long: String}
  SameSub{path: List<&2, String>, name: String}
  HelpSub{path: List<&2, String>}
  DefaultNotChoice{path: List<&2, String>, name: String, value: String}
  RequiredAfterOptional{path: List<&2, String>, name: String}

# one report when the flag is set, else none
def one(hit: Bool, err: SpecErr) -> List<&2, SpecErr>:
  match hit:
    case True{}:
      [err]
    case False{}:
      []

# two lists of reports, one after the other
def both(xs: List<&2, SpecErr>, ys: List<&2, SpecErr>) -> List<&2, SpecErr>:
  List.append(&2, SpecErr, xs, ys)

# whether a spelling, when there is one, is among those already seen
def spelled.seen(sp: Maybe<&2, String>, +seen: List<&2, String>) -> Bool:
  match sp:
    case None{}:
      False{}
    case Some{ss}:
      List.contains(~String, ~String.eq, seen, ss)

# the spellings seen, with this one when there is one
def spelled.add(sp: Maybe<&2, String>, seen: List<&2, String>) -> List<&2, String>:
  match sp:
    case None{}:
      seen
    case Some{ss}:
      ss <> seen

# a default outside a nonempty choices list
def args.default(
  dflt: Maybe<&2, String>,
  +cs: List<&2, String>,
  +path: List<&2, String>,
  +name: String
) -> List<&2, SpecErr>:
  match dflt:
    case None{}:
      []
    case Some{+vv}:
      one(Bool.and(Bool.not(List.is_empty(&2, String, cs)), Bool.not(C.allowed.ok(cs, vv))),
        DefaultNotChoice{path, name, vv})

# each argument's name and spellings against the earlier ones', and its
# default against its choices
def args.dups(
  args: List<&2, C.Arg>,
  +path: List<&2, String>,
  +names: List<&2, String>,
  +shorts: List<&2, String>,
  +longs: List<&2, String>
) -> List<&2, SpecErr>:
  match args:
    case Nil{}:
      []
    case Con{hh, tt}:
      C.Arg{+name, +short, +long, _k, _h, _r, C.Fallback{_e, dflt}, +cs} = hh
      both(one(List.contains(~String, ~String.eq, names, name), SameName{path, name}),
        both(one(spelled.seen(short, shorts), SameShort{path, C.text.of(short, "")}),
          both(one(spelled.seen(long, longs), SameLong{path, C.text.of(long, "")}),
            both(args.default(dflt, cs, path, name),
              args.dups(tt, path, name <> names, spelled.add(short, shorts),
                spelled.add(long, longs))))))

# the positionals in order: a rest before the last, and a required one after
# an optional one
def pos.order(
  pos: List<&2, C.Arg>,
  +path: List<&2, String>,
  +opt_seen: Bool
) -> List<&2, SpecErr>:
  match pos:
    case Nil{}:
      []
    case Con{hh, +tt}:
      C.Arg{+name, _s, _l, kind, _h, +req, _d, _c} = hh
      both(one(Bool.and(C.rest.is.kind(kind), Bool.not(List.is_empty(&2, C.Arg, tt))),
          RestNotLast{path, name}),
        both(one(Bool.and(req, opt_seen), RequiredAfterOptional{path, name}),
          pos.order(tt, path, Bool.or(opt_seen, Bool.not(req)))))

# each subcommand's name against the earlier ones', and against `help`
def subs.dups(
  subs: List<&2, C.Sub>,
  +path: List<&2, String>,
  +names: List<&2, String>
) -> List<&2, SpecErr>:
  match subs:
    case Nil{}:
      []
    case Con{hh, tt}:
      C.Sub{+name, _a, _g, _c} = hh
      both(one(List.contains(~String, ~String.eq, names, name), SameSub{path, name}),
        both(one(String.eq(name, "help"), HelpSub{path}),
          subs.dups(tt, path, name <> names)))

# one command's own reports
def cmd(
  +path: List<&2, String>,
  +args: List<&2, C.Arg>,
  subs: List<&2, C.Sub>
) -> List<&2, SpecErr>:
  both(args.dups(args, path, [], [], []),
    both(pos.order(C.pos_of(args), path, False{}), subs.dups(subs, path, [])))

# a name in front of a reversed path
def pushed(name: String, back: List<&2, String>) -> List<&2, String>:
  name <> back

# every subcommand's reports, each under its own path, depth first. The path
# is carried reversed, innermost name first, and read the right way round
# once per command
def forest(subs: List<&2, C.Sub>, +back: List<&2, String>) -> List<&2, SpecErr>:
  match subs:
    case Nil{}:
      []
    case Con{hh, tt}:
      C.Sub{+name, _a, +args, +kids} = hh
      +here = pushed(name, back)
      both(cmd(List.reverse(&2, String, here), args, kids),
        both(forest(kids, here), forest(tt, back)))

# every way the spec contradicts itself: the root's reports, then each
# subcommand's
def check(app: C.Cli) -> List<&2, SpecErr>:
  C.Cli{_n, _a, _v, +args, +subs} = app
  both(cmd([], args, subs), forest(subs, []))

# where a report is: the root, or a subcommand's path
def at.pick(root: Bool, +path: List<&2, String>) -> String:
  match root:
    case True{}:
      "spec: "
    case False{}:
      "spec, command '" ++ String.join(path, " ") ++ "': "

# where a report is
def at(+path: List<&2, String>) -> String:
  at.pick(List.is_empty(&2, String, path), path)

# a report as one line
def text(err: SpecErr) -> String:
  match err:
    case RestNotLast{path, name}:
      at(path) ++ "rest positional '" ++ name ++ "' is not the last positional"
    case SameName{path, name}:
      at(path) ++ "two arguments are named '" ++ name ++ "'"
    case SameShort{path, short}:
      at(path) ++ "two arguments are spelled '-" ++ short ++ "'"
    case SameLong{path, long}:
      at(path) ++ "two arguments are spelled '--" ++ long ++ "'"
    case SameSub{path, name}:
      at(path) ++ "two subcommands are named '" ++ name ++ "'"
    case HelpSub{path}:
      at(path) ++ "a subcommand is named 'help', which `parse` keeps for help"
    case DefaultNotChoice{path, name, value}:
      at(path) ++ "the default '" ++ value ++ "' of '" ++ name ++ "' is not one of its choices"
    case RequiredAfterOptional{path, name}:
      at(path) ++ "required positional '" ++ name ++ "' follows an optional one"

# how a program reads an argument: whether a flag is on (`on`), or its values
# (`get`, `get_all`)
type Want is Data:
  WantFlag{}
  WantValue{}

# one read a program makes: the command path, the argument's name, and how it
# reads it
type Read is Data:
  Read{path: List<&2, String>, name: String, want: Want}

# one read that does not fit the spec
type ReadErr is Data:
  NoCommand{path: List<&2, String>}
  NoArg{path: List<&2, String>, name: String}
  NotFlag{path: List<&2, String>, name: String}
  IsFlag{path: List<&2, String>, name: String}

# a read report when the flag is set, else none
def reads.one(hit: Bool, err: ReadErr) -> List<&2, ReadErr>:
  match hit:
    case True{}:
      [err]
    case False{}:
      []

# the arguments of a found command
def reads.args(here: Maybe<&2, C.Sub>) -> Maybe<&2, List<&2, C.Arg>>:
  match here:
    case None{}:
      None{}
    case Some{ss}:
      C.Sub{_n, _a, args, _s} = ss
      Some{args}

# the subcommand named `name` of a found command
def reads.down(here: Maybe<&2, C.Sub>, +name: String) -> Maybe<&2, C.Sub>:
  match here:
    case None{}:
      None{}
    case Some{ss}:
      C.Sub{_n, _a, _g, subs} = ss
      C.find_sub(subs, name)

# the arguments of the command a path names below the command found, each
# name a subcommand of the command before it, or None
def reads.cmd(path: List<&2, String>, here: Maybe<&2, C.Sub>) -> Maybe<&2, List<&2, C.Arg>>:
  match path:
    case Nil{}:
      reads.args(here)
    case Con{+hh, tt}:
      reads.cmd(tt, reads.down(here, hh))

# whether an argument of this kind is a flag
def reads.flag(kk: C.ArgKind) -> Bool:
  match kk:
    case C.Flag{}:
      True{}
    case C.Opt{}:
      False{}
    case C.Pos{}:
      False{}
    case C.Rest{}:
      False{}
    case C.Many{}:
      False{}

# a read of an argument that is, or is not, a flag
def reads.want(want: Want, flag: Bool, +path: List<&2, String>, +name: String) -> List<&2, ReadErr>:
  match want:
    case WantFlag{}:
      reads.one(Bool.not(flag), NotFlag{path, name})
    case WantValue{}:
      reads.one(flag, IsFlag{path, name})

# a read of the argument found under its name, or of none
def reads.arg(found: Maybe<&2, C.Arg>, want: Want, +path: List<&2, String>, +name: String) -> List<&2, ReadErr>:
  match found:
    case None{}:
      [NoArg{path, name}]
    case Some{aa}:
      C.Arg{_n, _s, _l, kind, _h, _r, _d, _c} = aa
      reads.want(want, reads.flag(kind), path, name)

# a read of the command a path names, or of none
def reads.at(
  cmd: Maybe<&2, List<&2, C.Arg>>,
  want: Want,
  +path: List<&2, String>,
  +name: String
) -> List<&2, ReadErr>:
  match cmd:
    case None{}:
      [NoCommand{path}]
    case Some{args}:
      reads.arg(C.by_name(args, name), want, path, name)

# what is wrong with one read, or nothing
def read(app: C.Cli, rr: Read) -> List<&2, ReadErr>:
  C.Cli{+bin, +about, _v, args, subs} = app
  Read{+path, +name, want} = rr
  reads.at(reads.cmd(path, Some{C.Sub{bin, about, args, subs}}), want, path, name)

# what is wrong with each read, in order
def check_reads(+app: C.Cli, rs: List<&2, Read>) -> List<&2, ReadErr>:
  match rs:
    case Nil{}:
      []
    case Con{hh, tt}:
      List.append(&2, ReadErr, read(app, hh), check_reads(app, tt))

# where a read report is
def read.at(+path: List<&2, String>) -> String:
  Bool.pick(String, List.is_empty(&2, String, path), "read: ", "read, command '" ++ String.join(path, " ") ++ "': ")

# a read report as one line
def read_text(err: ReadErr) -> String:  # noqa: L001 a message: its words are not a guarantee
  match err:
    case NoCommand{+path}:
      read.at(path) ++ "no command is named so"
    case NoArg{+path, name}:
      read.at(path) ++ "no argument is named '" ++ name ++ "'"
    case NotFlag{+path, name}:
      read.at(path) ++ "'" ++ name ++ "' is read as a flag, but it is not one"
    case IsFlag{+path, name}:
      read.at(path) ++ "'" ++ name ++ "' is read for a value, but it is a flag"
