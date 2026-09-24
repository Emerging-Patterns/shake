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
      C.Arg{+name, +short, +long, _k, _h, _r, dflt, +cs} = hh
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
