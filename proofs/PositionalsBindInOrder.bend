# proofs of laws/PositionalsBindInOrder.bend
import Base
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ../laws/Kept.bend as L1
import ../laws/PositionalsBindInOrder.bend as Laws
import ./lemmas/BindingsKept.bend as M1
import ./lemmas/WalkSteps.bend as M2

def Laws.start_state(_name, _about, _version, _args, _subs):
  {==}

# keeping an argument in front of two lists is keeping it in front of the first
def pof.put_app(
  keep: Bool,
  +hh: S.Arg,
  +aa: List<&2, S.Arg>,
  +bb: List<&2, S.Arg>
) -> {S.pos_of.put(keep, hh, List.append(&2, S.Arg, aa, bb))
    == List.append(&2, S.Arg, S.pos_of.put(keep, hh, aa), bb) : List<&2, S.Arg>}:
  match keep:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.pos_of_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, S.Arg>, S.pos_of.put(S.pos.is(hh), hh, S.pos_of(List.append(&2, S.Arg, tt, ys))),
        S.pos_of.put(S.pos.is(hh), hh, List.append(&2, S.Arg, S.pos_of(tt), S.pos_of(ys))),
        List.append(&2, S.Arg, S.pos_of.put(S.pos.is(hh), hh, S.pos_of(tt)), S.pos_of(ys)),
        Equal.cong(List<&2, S.Arg>, List<&2, S.Arg>, zs => S.pos_of.put(S.pos.is(hh), hh, zs),
          S.pos_of(List.append(&2, S.Arg, tt, ys)), List.append(&2, S.Arg, S.pos_of(tt), S.pos_of(ys)),
          Laws.pos_of_app(tt, ys)),
        pof.put_app(S.pos.is(hh), hh, S.pos_of(tt), S.pos_of(ys)))

def Laws.pos_of_pos(aa, h_pos):
  ee = Equal.sym(Bool, S.pos.is(aa), True{}, h_pos)
  %ee : {S.pos_of.put(_, aa, []) == [aa] : List<&2, S.Arg>}
  {==}

def Laws.pos_of_opt(aa, h_opt):
  ee = Equal.sym(Bool, S.pos.is(aa), False{}, h_opt)
  %ee : {S.pos_of.put(_, aa, []) == [] : List<&2, S.Arg>}
  {==}

# after a positional is bound, `help` reaches the positional it binds
def hw.step(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>}
) -> {S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, True{}})
    == S.parse.take_pos("help", args, up, subs, path, bs, pos, False{}) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, "help"), None{}, h_sub)
  %ee : {S.parse.word.go(_, "help", args, up, subs, path, bs, pos, False{}, True{})
    == S.parse.take_pos("help", args, up, subs, path, bs, pos, False{}) : S.St}
  {==}

# `help` taken by the next positional
def hw.full(
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +name: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +rest: List<&2, S.Arg>,
  h_sub: {S.find_sub(subs, "help") == None{} : Maybe<&2, S.Sub>},
  h_ok: {S.allowed(cs, "help") == True{} : Bool}
) -> {S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt,
    cs} <> rest,
      False{}, True{}})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}} : S.St}:
  +pp = {S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest : List<&2, S.Arg>}
  Equal.trans(S.St, S.parse.step("help", S.St{S.Free{}, args, up, subs, path, bs, pp, False{}, True{}}),
    S.parse.take_pos("help", args, up, subs, path, bs, pp, False{}),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    hw.step(args, up, subs, path, bs, pp, h_sub),
    M2.pos.take("help", args, up, subs, path, bs, False{}, name, sh, lo, kind, hp, req, dflt, cs, rest, h_ok))

def Laws.help_word_next(
  spec,
  pre,
  args,
  up,
  subs,
  path,
  bs,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  h_at,
  h_sub,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, True{}}
    : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ["help"]), S.parse.start(spec)), S.parse.step("help", st),
    S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
      S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
        S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
    M2.kept.stepped(spec, pre, "help", st, h_at),
    hw.full(args, up, subs, path, bs, name, sh, lo, kind, hp, req, dflt, cs, rest, h_sub, h_ok))

def Laws.help_word_binds(
  spec,
  pre,
  more,
  args,
  up,
  subs,
  path,
  bs,
  name,
  sh,
  lo,
  kind,
  hp,
  req,
  dflt,
  cs,
  rest,
  found,
  h_at,
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, S.Arg{name, sh, lo, kind, hp, req, dflt, cs} <> rest, False{}, True{}}
    : S.St}
  L1.kept(spec, pre, more, "help", st, args, up, path, name, "help", bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.step("help", st),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, "help"} <> bs,
        S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
          S.Arg{name, sh, lo, kind, hp, req, dflt, cs}, rest), False{}, True{}},
      hw.full(args, up, subs, path, bs, name, sh, lo, kind, hp, req, dflt, cs, rest, h_sub, h_ok)),
    h_done)
