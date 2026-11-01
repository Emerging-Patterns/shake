# proofs of laws/RestTakesRemainingWords.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
import ../laws/KeptAll.bend as L1
import ../laws/RestTakesRemainingWords.bend as Laws
import ../laws/defs/ValuesAtPath.bend as D1
import ./lemmas/BindingsKept.bend as M1
import ./lemmas/WalkSteps.bend as M2

# a rest positional, as the walker holds it
def rest.arg(
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>
) -> S.Arg:
  S.Arg{nm, sh, lo, S.Rest{}, hp, req, dflt, cs}

# before `--`, plain words bind the rest one by one
def rest.walk(
  fs: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +h_plain: {Walk.all_plain(fs) == True{} : Bool},
  +h_sub: {Walk.wk.unfound(subs, fs) == True{} : Bool},
  +h_ok: {Laws.all_allowed(cs, fs) == True{} : Bool}
) -> {S.parse.walk(fs, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
      seen})
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)],
      False{}, Walk.wk.seen(fs, seen)} : S.St}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = Walk.wk.and_l(Walk.plain_word(ww), Walk.all_plain(tl), h_plain)
      su = Walk.wk.and_l(Maybe.is_none(&2, S.Sub, S.find_sub(subs, ww)), Walk.wk.unfound(subs, tl), h_sub)
      ok = Walk.wk.and_l(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok)
      ee = Equal.sym(S.St,
        S.parse.step(ww, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
          seen}),
        S.St{S.Free{}, args, up, subs, path, S.Bind{nm, ww} <> bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
          True{}},
        M2.pos.step(ww, args, up, subs, path, bs, seen, nm, sh, lo, S.Rest{}, hp, req, dflt, cs, [],
          Walk.wk.plain_dd(ww, pl), Walk.wk.plain_help(ww, pl), Walk.wk.plain_dash(ww, pl),
          Walk.wk.none_of(S.find_sub(subs, ww), su), ok))
      %ee : {S.parse.walk(tl, _)
        == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(tl, nm, S.Bind{nm, ww} <> bs),
          [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, Walk.wk.seen(tl, True{})} : S.St}
      rest.walk(tl, args, up, subs, path, S.Bind{nm, ww} <> bs, True{}, nm, sh, lo, hp, req, dflt, cs,
        Walk.wk.and_r(Walk.plain_word(ww), Walk.all_plain(tl), h_plain),
        Walk.wk.and_r(Maybe.is_none(&2, S.Sub, S.find_sub(subs, ww)), Walk.wk.unfound(subs, tl), h_sub),
        Walk.wk.and_r(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok))

# after `--`, every word binds the rest one by one
def rest.raw(
  fs: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  +nm: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +hp: String,
  +req: Bool,
  +dflt: S.Fallback,
  +cs: List<&2, String>,
  +h_ok: {Laws.all_allowed(cs, fs) == True{} : Bool}
) -> {S.parse.walk(fs, S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
      seen})
    == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)],
      True{}, Walk.wk.seen(fs, seen)} : S.St}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      ee = Equal.sym(S.St,
        S.parse.take_pos(ww, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}),
        S.St{S.Free{}, args, up, subs, path, S.Bind{nm, ww} <> bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
          True{}},
        M2.pos.take(ww, args, up, subs, path, bs, True{}, nm, sh, lo, S.Rest{}, hp, req, dflt, cs, [],
          Walk.wk.and_l(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok)))
      %ee : {S.parse.walk(tl, _)
        == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(tl, nm, S.Bind{nm, ww} <> bs),
          [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, Walk.wk.seen(tl, True{})} : S.St}
      rest.raw(tl, args, up, subs, path, S.Bind{nm, ww} <> bs, True{}, nm, sh, lo, hp, req, dflt, cs,
        Walk.wk.and_r(S.allowed(cs, ww), Laws.all_allowed(cs, tl), h_ok))

def Laws.rest_next(
  spec,
  pre,
  fs,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  h_at,
  h_plain,
  h_sub,
  h_ok
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)), S.parse.walk(fs, st),
    S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
      Walk.wk.seen(fs, seen)},
    M2.rest.after(spec, pre, fs, st, h_at),
    rest.walk(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_plain, h_sub, h_ok))

def Laws.rest_raw_next(spec, pre, fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_at, h_ok):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, seen} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, fs), S.parse.start(spec)), S.parse.walk(fs, st),
    S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
      Walk.wk.seen(fs, seen)},
    M2.rest.after(spec, pre, fs, st, h_at),
    rest.raw(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_ok))

# the bindings a walk pushes onto some it had are those it pushes onto none,
# then those
def rest.pushed(
  fs: List<&2, String>,
  +nm: String,
  +acc: List<&2, S.Bind>,
  +bs: List<&2, S.Bind>
) -> {Walk.wk.pushed(fs, nm, List.append(&2, S.Bind, acc, bs))
    == List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, acc), bs) : List<&2, S.Bind>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, tl}:
      rest.pushed(tl, nm, S.Bind{nm, ww} <> acc, bs)

# one binding of `nm` per word, in order
def rest.bs(fs: List<&2, String>, +nm: String) -> List<&2, S.Bind>:
  match fs:
    case Nil{}:
      []
    case Con{+ww, tl}:
      S.Bind{nm, ww} <> rest.bs(tl, nm)

# the pushed bindings, reversed onto a list, are one per word in order
def rest.rev(
  fs: List<&2, String>,
  +nm: String,
  +acc: List<&2, S.Bind>,
  +out: List<&2, S.Bind>
) -> {List.reverse.go(&2, S.Bind, Walk.wk.pushed(fs, nm, acc), out)
    == List.reverse.go(&2, S.Bind, acc, List.append(&2, S.Bind, rest.bs(fs, nm), out)) : List<&2, S.Bind>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, tl}:
      rest.rev(tl, nm, S.Bind{nm, ww} <> acc, out)

# bindings with nothing after them
def rest.nil_b(bs: List<&2, S.Bind>) -> {List.append(&2, S.Bind, bs, []) == bs : List<&2, S.Bind>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      Equal.cong(List<&2, S.Bind>, List<&2, S.Bind>, xs => hh <> xs, List.append(&2, S.Bind, tt,
          []), tt, rest.nil_b(tt))

# one binding of `nm` per word reads back the words
def rest.vals(fs: List<&2, String>, +nm: String) -> {S.get_all.bind(rest.bs(fs, nm), nm) == fs : List<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      ee = Equal.sym(Bool, String.eq(nm, nm), True{}, Eq.string_eq_self(nm))
      %ee : {S.get_all.bind.hit(_, ww, S.get_all.bind(rest.bs(tl, nm), nm)) == ww <> tl : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, xs => ww <> xs, S.get_all.bind(rest.bs(tl, nm), nm), tl,
        rest.vals(tl, nm))

# the rest's values the words pushed, read back in order, are the words
def rest.read(
  +fs: List<&2, String>,
  +nm: String
) -> {S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm) == fs : List<&2, String>}:
  Equal.trans(List<&2, String>, S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm),
    S.get_all.bind(rest.bs(fs, nm), nm), fs,
    Equal.cong(List<&2, S.Bind>, List<&2, String>, xs => S.get_all.bind(xs, nm),
      List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), rest.bs(fs, nm),
      Equal.trans(List<&2, S.Bind>, List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])),
        List.append(&2, S.Bind, rest.bs(fs, nm), []), rest.bs(fs, nm), rest.rev(fs, nm, [], []),
        rest.nil_b(rest.bs(fs, nm)))),
    rest.vals(fs, nm))

# what `rest_binds` claims
def rest.ty(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nm: String,
  +fs: List<&2, String>,
  +bs: List<&2, S.Bind>
) -> Type:
  &after: List<&2, String> -> {D1.all_at(found, path, nm)
    == Some{List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, bs), nm), List.append(&2, String,
        fs, after))}
    : Maybe<&2, List<&2, String>>}

# the pushed bindings read back as the words
def rest.back(
  +found: Shake.Matched,
  +path: List<&2, String>,
  +nm: String,
  +fs: List<&2, String>,
  +bs: List<&2, S.Bind>,
  ww: M1.kept_all.ty(found, path, nm, Walk.wk.pushed(fs, nm, []), bs)
) -> rest.ty(found, path, nm, fs, bs):
  (ax, ee) = ww
  +after = {ax : List<&2, String>}
  +gb = S.get_all.bind(List.reverse(&2, S.Bind, bs), nm)
  (after, Equal.trans(Maybe<&2, List<&2, String>>, D1.all_at(found, path, nm),
    Some{List.append(&2, String, gb,
      List.append(&2, String, S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm), after))},
    Some{List.append(&2, String, gb, List.append(&2, String, fs, after))}, ee,
    Equal.cong(List<&2, String>, Maybe<&2, List<&2, String>>,
      xs => Some{List.append(&2, String, gb, List.append(&2, String, xs, after))},
      S.get_all.bind(List.reverse(&2, S.Bind, Walk.wk.pushed(fs, nm, [])), nm), fs, rest.read(fs, nm))))

# the view after the words, from the walker's state after them
def rest.view(
  +fs: List<&2, String>,
  +st: S.St,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +nm: String,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  ew: {S.parse.walk(fs, st) == S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), pos, raw, seen} : S.St}
) -> {Grow.view(S.parse.walk(fs, st))
    == Grow.View{args, up, path, List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs)} : Grow.View}:
  Equal.trans(Grow.View, Grow.view(S.parse.walk(fs, st)), Grow.View{args, up, path, Walk.wk.pushed(fs, nm, bs)},
    Grow.View{args, up, path, List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs)},
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx), S.parse.walk(fs, st),
      S.St{S.Free{}, args, up, subs, path, Walk.wk.pushed(fs, nm, bs), pos, raw, seen}, ew),
    Equal.cong(List<&2, S.Bind>, Grow.View, xs => Grow.View{args, up, path, xs}, Walk.wk.pushed(fs, nm, bs),
      List.append(&2, S.Bind, Walk.wk.pushed(fs, nm, []), bs), rest.pushed(fs, nm, [], bs)))

def Laws.rest_binds(
  spec,
  pre,
  fs,
  more,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  found,
  h_at,
  h_plain,
  h_sub,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{}, seen} : S.St}
  rest.back(found, path, nm, fs, bs,
    L1.kept_all(spec, pre, fs, more, st, args, up, path, Walk.wk.pushed(fs, nm, []), bs, nm, found, h_at,
      rest.view(fs, st, args, up, subs, path, bs, nm, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], False{},
        Walk.wk.seen(fs, seen),
        rest.walk(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_plain, h_sub, h_ok)),
      h_done))

def Laws.rest_raw_binds(
  spec,
  pre,
  fs,
  more,
  args,
  up,
  subs,
  path,
  bs,
  seen,
  nm,
  sh,
  lo,
  hp,
  req,
  dflt,
  cs,
  found,
  h_at,
  h_ok,
  h_done
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{}, seen} : S.St}
  rest.back(found, path, nm, fs, bs,
    L1.kept_all(spec, pre, fs, more, st, args, up, path, Walk.wk.pushed(fs, nm, []), bs, nm, found, h_at,
      rest.view(fs, st, args, up, subs, path, bs, nm, [rest.arg(nm, sh, lo, hp, req, dflt, cs)], True{},
        Walk.wk.seen(fs, seen), rest.raw(fs, args, up, subs, path, bs, seen, nm, sh, lo, hp, req, dflt, cs, h_ok)),
      h_done))
