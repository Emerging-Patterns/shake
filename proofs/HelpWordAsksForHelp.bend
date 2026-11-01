# proofs of laws/HelpWordAsksForHelp.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../laws/HelpWalk.bend as L1
import ../laws/HelpWordAsksForHelp.bend as Laws
import ./lemmas/HelpPathWalk.bend as M1
import ./lemmas/WalkSteps.bend as M2

def Laws.help_step(spec, pre, args, up, subs, path, bs, pos, h_at):
  M2.kept.stepped(spec, pre, "help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}, h_at)

# the words leave the walker reading the help path `path`
def hp.ended(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>
) -> Type:
  &kids: List<&2, S.Sub> -> {S.parse.walk(ws, S.parse.start(spec))
    == S.St{S.Help{}, args, up, kids, path, bs, pos, False{}, False{}} : S.St}

# a help walk that ends reading its path fails with NeedHelp of it
def hp.need(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  ww: hp.ended(spec, ws, args, up, path, bs, pos)
) -> {Shake.parse(spec, ws) == Fail{S.NeedHelp{path}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}:
  (k1, e1) = ww
  Equal.cong(S.St, Result<&2, &2, S.ParseErr, S.Matched>, xx => S.version.res(spec, S.parse.finish(xx)),
    S.parse.walk(ws, S.parse.start(spec)),
    S.St{S.Help{}, args, up, k1, path, bs, pos, False{}, False{}}, e1)

def Laws.help_path(spec, pre, ns, args, up, subs, path, bs, pos, h_at, h_ns):
  +ph = List.append(&2, String, pre, ["help"])
  hp.need(spec, List.append(&2, String, ph, ns), args, up, List.append(&2, String, path, ns), bs, pos,
    L1.help_walk(spec, ph, ns, args, up, subs, path, bs, pos, False{}, False{},
      Laws.help_step(spec, pre, args, up, subs, path, bs, pos, h_at), h_ns))

# a free walker with no long `help` reads `--help` as `help`
def dash_help.step(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  h_none: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
) -> {S.parse.step("--help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}})
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}:
  ee = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, "help"), None{}, h_none)
  %ee : {S.parse.take_long.found(_, "help", None{}, "--help", args, up, subs, path, bs, pos, False{}, False{})
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  {==}

def Laws.dash_help_step(spec, pre, args, up, subs, path, bs, pos, h_at, h_none):
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ["--help"]), S.parse.start(spec)),
    S.parse.step("--help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}),
    S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}},
    M2.kept.stepped(spec, pre, "--help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}, h_at),
    dash_help.step(args, up, subs, path, bs, pos, h_none))

def Laws.dash_help_path(spec, pre, ns, args, up, subs, path, bs, pos, h_at, h_none, h_ns):
  +ph = List.append(&2, String, pre, ["--help"])
  hp.need(spec, List.append(&2, String, ph, ns), args, up, List.append(&2, String, path, ns), bs, pos,
    L1.help_walk(spec, ph, ns, args, up, subs, path, bs, pos, False{}, False{},
      Laws.dash_help_step(spec, pre, args, up, subs, path, bs, pos, h_at, h_none), h_ns))

# a free walker whose command spells neither `-h` nor `--help` reads `-h` as
# `help`
def short_help.step(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  h_short: {S.by_short(args, "h") == None{} : Maybe<&2, S.Arg>},
  h_long: {S.by_long(args, "help") == None{} : Maybe<&2, S.Arg>}
) -> {S.parse.step("-h", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}})
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}:
  e1 = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, "h"), None{}, h_short)
  %e1 : {S.parse.take_short.go(Bool.and(True{}, Bool.and(True{}, Bool.and(Maybe.is_none(&2, S.Arg, _),
      Maybe.is_none(&2, S.Arg, S.by_long(args, "help"))))), "h", "-h", args, up, subs, path, bs, pos, False{},
      False{})
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  e2 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, "help"), None{}, h_long)
  %e2 : {S.parse.take_short.go(Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Maybe.is_none(&2, S.Arg, _)))),
      "h", "-h", args, up, subs, path, bs, pos, False{}, False{})
    == S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}} : S.St}
  {==}

def Laws.short_help_step(spec, pre, args, up, subs, path, bs, pos, h_at, h_short, h_long):
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ["-h"]), S.parse.start(spec)),
    S.parse.step("-h", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}),
    S.St{S.Help{}, args, up, subs, path, bs, pos, False{}, False{}},
    M2.kept.stepped(spec, pre, "-h", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, False{}}, h_at),
    short_help.step(args, up, subs, path, bs, pos, h_short, h_long))

def Laws.short_help_path(spec, pre, ns, args, up, subs, path, bs, pos, h_at, h_short, h_long, h_ns):
  +ph = List.append(&2, String, pre, ["-h"])
  hp.need(spec, List.append(&2, String, ph, ns), args, up, List.append(&2, String, path, ns), bs, pos,
    L1.help_walk(spec, ph, ns, args, up, subs, path, bs, pos, False{}, False{},
      Laws.short_help_step(spec, pre, args, up, subs, path, bs, pos, h_at, h_short, h_long), h_ns))
