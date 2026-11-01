# one walker step: entering a subcommand, a plain word, a positional, a long
# option
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S
import ../../src/walk.bend as Walk
import ../../laws/DropZero.bend as L1
import ../../laws/LongArgStep.bend as L2
import ../../laws/PrefixEmpty.bend as L3
import ../../laws/UnknownLongDies.bend as L4
import ../../laws/UnknownLongStep.bend as L5
import ../../laws/WalkAppend.bend as L6
import ../../laws/defs/WalkerFailure.bend as D1

def L6.walk_append(xs, ys, st):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      L6.walk_append(tt, ys, S.parse.step(hh, st))

def L3.prefix_empty(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def L1.drop_zero(ss):
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

def L5.unknown_long_step(
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_dd,
  h_cut,
  h_name,
  h_none,
  h_lh
):
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, L3.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, L1.drop_zero(body))
  %ed : {S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e3 = Equal.sym(Bool, String.is_empty(name), False{}, h_name)
  %e3 : {S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e4 = Equal.sym(Maybe<&2, S.Arg>, S.by_long(args, name), None{}, h_none)
  %e4 : {S.parse.take_long.found(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  e5 = Equal.sym(Bool, S.long_help(name, val, seen), False{}, h_lh)
  %e5 : {S.parse.take_long.help(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  {==}

def L4.unknown_long_dies(
  spec,
  pre,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_name,
  h_none,
  h_lh
):
  e1 = Equal.sym(S.St,
    S.parse.walk(List.append(&2, String, pre, ["--" ++ body]), S.parse.start(spec)),
    S.parse.walk(["--" ++ body], S.parse.walk(pre, S.parse.start(spec))),
    L6.walk_append(pre, ["--" ++ body], S.parse.start(spec)))
  %e1 : {D1.dead_of(_) == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(S.St,
    S.parse.walk(pre, S.parse.start(spec)),
    S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
    h_at)
  %e2 : {D1.dead_of(S.parse.walk(["--" ++ body], _)) == Some{S.UnknownFlag{path, "--" ++ body}}
    : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(S.St, S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}),
    S.St{S.Dead{S.UnknownFlag{path, "--" ++ body}}, args, up, subs, path, bs, pos, False{}, seen},
    L5.unknown_long_step(body, name, val, args, up, subs, path, bs, pos, seen,
      h_dd, h_cut, h_name, h_none, h_lh))
  %e3 : {D1.dead_of(_) == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

def L2.long_arg_step(
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_dd,
  h_cut,
  h_name
):
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, L3.prefix_empty(body))
  %e0 : {S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen)
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  ed = Equal.sym(String, String.drop(body, 0n), body, L1.drop_zero(body))
  %ed : {S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  e3 = Equal.sym(Bool, String.is_empty(name), False{}, h_name)
  %e3 : {S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.take_long.found(S.by_long(args, name), name, val, "--" ++ body, args, up, subs, path, bs, pos, False{},
        seen) : S.St}
  {==}

# the walk through `tok` is one step from where the words before it stood
def kept.stepped(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +tok: String,
  +st: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)) == S.parse.step(tok, st) : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)),
    S.parse.walk([tok], S.parse.walk(pre, S.parse.start(spec))), S.parse.step(tok, st),
    L6.walk_append(pre, [tok], S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk([tok], xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))

# an allowed value taken by the next positional, through `take_choice`
def pos.take(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +raw: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_ok: {S.allowed(cs, tok) == True{} : Bool}
) -> {S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, raw)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{}} : S.St}:
  e2 = Equal.sym(Bool, S.allowed(cs, tok), True{}, h_ok)
  %e2 : {S.parse.take_choice(_, name, tok, args, up, subs, path, bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), raw, True{}} : S.St}
  {==}

# a plain word taken by the next positional
def pos.step(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool},
  h_sub: {S.find_sub(subs, tok) == None{} : Maybe<&2, S.Sub>},
  h_ok: {S.allowed(cs, tok) == True{} : Bool}
) -> {S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs,
      S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}:
  Equal.trans(S.St,
    S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest,
      False{}, seen}),
    S.parse.take_pos(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    Walk.wk.word_step(tok, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, seen,
      h_dd, h_help, h_dash, h_sub),
    pos.take(tok, args, up, subs, path, bs, False{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))

# the words before `fs`, then `fs`, from where the words before left the walker
def rest.after(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +fs: List<&2, String>,
  +st: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)) == S.parse.walk(fs, st) : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)),
    S.parse.walk(fs, S.parse.walk(pre, S.parse.start(spec))), S.parse.walk(fs, st),
    L6.walk_append(pre, fs, S.parse.start(spec)),
    Equal.cong(S.St, S.St, xx => S.parse.walk(fs, xx), S.parse.walk(pre, S.parse.start(spec)), st, h_at))

# a plain word before `--` is read as a word: a subcommand or a positional
def enter.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq(tok, "--") == False{} : Bool},
  h_help: {String.eq(tok, "help") == False{} : Bool},
  +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
) -> {S.parse.step(tok, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen) : S.St}:
  +rhs = S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e2 = Equal.sym(Bool, String.eq(tok, "help"), False{}, h_help)
  %e2 : {S.parse.step.help(Bool.and(_, Bool.not(seen)), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, Walk.wk.dash(tok, h_dash))
  %e3 : {S.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {S.parse.step.kind.go(False{}, _, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  {==}

# a found subcommand, entered or refused, as the first blocking positional says
def enter.go(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +sub: S.Sub,
  h_sub: {S.find_sub(subs, tok) == Some{sub} : Maybe<&2, S.Sub>}
) -> {S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, tok), Some{sub}, h_sub)
  %ee : {S.parse.word.go(_, tok, args, up, subs, path, bs, pos, False{}, seen)
    == S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen) : S.St}
  {==}
