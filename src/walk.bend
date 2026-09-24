# shake/walk: lemmas about the walker, one word at a time. They were first
# proved in bolt's bolt/PROOF.bend, against shake's walker, for bolt's own
# `files` positional; here they are general over the rest positional, beside
# the walker, so SHAKE rows can cite them and bolt need not unfold shake
# (docs/rfc/shake-walker-proofs.md, WP0).
import Base
import ./cli.bend as Shake

# a word read as a positional value: neither `--` nor `help`, and not
# starting with `-`
def plain_word(+ww: String) -> Bool:
  Bool.not(Bool.or(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-"))))

# whether every word is plain
def all_plain(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(plain_word(ww), all_plain(rest))  # noqa: U002 a law premise, never run; the proofs read Bool.and

# Unit for False, Empty for True: a motive that tells them apart
def wk.false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law wk.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def wk.false_true(e):
  %e : wk.false_ty(_)
  Unit{}

# True is never False
law wk.true_false:
  for e: {True{} == False{} : Bool}
  Empty

def wk.true_false(e):
  wk.false_true(Equal.sym(Bool, True{}, False{}, e))

# the left of a true nor is false
law wk.nor_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {a == False{} : Bool}

def wk.nor_l(a, _b, h):
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, wk.false_true(h))
    case False{}:
      {==}

# the right of a true nor is not true
law wk.nor_r:
  for a: Bool
  for b: Bool
  for h: {Bool.not(Bool.or(a, b)) == True{} : Bool}
  {Bool.not(b) == True{} : Bool}

def wk.nor_r(a, b, h):
  match a:
    case True{}:
      Empty.absurd({Bool.not(b) == True{} : Bool}, wk.false_true(h))
    case False{}:
      h

# a Bool whose negation is true is false
law wk.not_true:
  for b: Bool
  for h: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def wk.not_true(b, h):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, wk.false_true(h))
    case False{}:
      {==}

# the left of a true and is true
law wk.and_l:
  for a: Bool
  for -b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def wk.and_l(a, _b, h):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, wk.false_true(h))
    case True{}:
      {==}

# the right of a true and is true
law wk.and_r:
  for a: Bool
  for b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def wk.and_r(a, b, h):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, wk.false_true(h))
    case True{}:
      h

# two true Bools make a true and
law wk.and_true:
  for a: Bool
  for b: Bool
  for ha: {a == True{} : Bool}
  for hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def wk.and_true(a, b, ha, hb):
  e = Equal.sym(Bool, a, True{}, ha)
  %e : {Bool.and(_, b) == True{} : Bool}
  hb

# a Maybe that is none is None
law wk.none_of:
  for mm: Maybe<&2, Shake.Sub>
  for h: {Maybe.is_none(&2, Shake.Sub, mm) == True{} : Bool}
  {mm == None{} : Maybe<&2, Shake.Sub>}

def wk.none_of(mm, h):
  match mm:
    case None{}:
      {==}
    case Some{s}:
      Empty.absurd({Some{s} == None{} : Maybe<&2, Shake.Sub>}, wk.false_true(h))

# a word past its first `-` test: the `--` test fails wherever the `-` one does
law wk.dash.if:
  for b: Bool
  for xt: String
  for h: {String.starts_with.if(xt, "", b) == False{} : Bool}
  {String.starts_with.if(xt, "-", b) == False{} : Bool}

def wk.dash.if(b, xt, h):
  match b:
    case False{}:
      {==}
    case True{}:
      match xt:
        case SNil{}:
          Empty.absurd({String.starts_with.if(SNil{}, "-", True{}) == False{} : Bool}, wk.true_false(h))
        case SCon{x, t}:
          Empty.absurd({String.starts_with.if(SCon{x, t}, "-", True{}) == False{} : Bool}, wk.true_false(h))

# a word that does not start with `-` does not start with `--`
law wk.dash:
  for ww: String
  for h: {String.starts_with(ww, "-") == False{} : Bool}
  {String.starts_with(ww, "--") == False{} : Bool}

def wk.dash(ww, h):
  match ww:
    case SNil{}:
      {==}
    case SCon{+x, xt}:
      wk.dash.if(Char.is_eq(x, '-'), xt, h)

# a plain word is not `--`
law wk.plain_dd:
  for +ww: String
  for h: {plain_word(ww) == True{} : Bool}
  {String.eq(ww, "--") == False{} : Bool}

def wk.plain_dd(ww, h):
  wk.nor_l(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)

# a plain word is not `help`
law wk.plain_help:
  for +ww: String
  for h: {plain_word(ww) == True{} : Bool}
  {String.eq(ww, "help") == False{} : Bool}

def wk.plain_help(ww, h):
  wk.nor_l(String.eq(ww, "help"), String.starts_with(ww, "-"),
    wk.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h))

# a plain word does not start with `-`
law wk.plain_dash:
  for +ww: String
  for h: {plain_word(ww) == True{} : Bool}
  {String.starts_with(ww, "-") == False{} : Bool}

def wk.plain_dash(ww, h):
  wk.not_true(String.starts_with(ww, "-"),
    wk.nor_r(String.eq(ww, "help"), String.starts_with(ww, "-"),
      wk.nor_r(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-")), h)))

# a rest positional with no choices
def wk.rest(+nm: String, +hlp: String, +req: Bool, +dflt: Maybe<&2, String>) -> Shake.Arg:
  Shake.Arg{nm, None{}, None{}, Shake.Rest{}, hlp, req, dflt, []}

# the binds a walk pushes for a rest named `nm`, onto the ones it had, newest
# first
def wk.pushed(fs: List<&2, String>, +nm: String, bs: List<&2, Shake.Bind>) -> List<&2, Shake.Bind>:
  match fs:
    case Nil{}:
      bs
    case Con{ff, rest}:
      wk.pushed(rest, nm, Shake.Bind{nm, ff} <> bs)

# whether a walker has seen a positional, after the words
def wk.seen(fs: List<&2, String>, seen: Bool) -> Bool:
  match fs:
    case Nil{}:
      seen
    case Con{_ff, rest}:
      wk.seen(rest, True{})

# whether no word names one of the subcommands
def wk.unfound(+subs: List<&2, Shake.Sub>, ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)),
        wk.unfound(subs, rest))  # noqa: U002 a law premise, never run

# a word that is not `--`, not `help`, not a flag and no subcommand here
# reaches the positional it binds
law wk.word_step:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  for h_dd: {String.eq(tok, "--") == False{} : Bool}
  for h_help: {String.eq(tok, "help") == False{} : Bool}
  for +h_dash: {String.starts_with(tok, "-") == False{} : Bool}
  for h_sub: {Shake.find_sub(subs, tok) == None{} : Maybe<&2, Shake.Sub>}
  {Shake.parse.step(tok, Shake.St{Shake.Free{}, args, up, subs, path, bs, pos, False{}, seen})
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}

def wk.word_step(tok, args, up, subs, path, bs, pos, seen, h_dd, h_help, h_dash, h_sub):
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {Shake.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}
  e2 = Equal.sym(Bool, String.eq(tok, "help"), False{}, h_help)
  %e2 : {Shake.parse.step.help(Bool.and(_, Bool.not(seen)), tok, args, up, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, wk.dash(tok, h_dash))
  %e3 : {Shake.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, up, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {Shake.parse.step.kind.go(False{}, _, tok, args, up, subs, path, bs, pos, seen)
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}
  e5 = Equal.sym(Maybe<&2, Shake.Sub>, Shake.find_sub(subs, tok), None{}, h_sub)
  %e5 : {Shake.parse.word.go(_, tok, args, up, subs, path, bs, pos, False{}, seen)
    == Shake.parse.take_pos(tok, args, up, subs, path, bs, pos, False{}) : Shake.St}
  {==}

# plain words, none a subcommand here, each bind the rest positional once more
law wk.walk_plain:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  for +nm: String
  for +hlp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for +seen: Bool
  for +hp: {all_plain(fs) == True{} : Bool}
  for +hu: {wk.unfound(subs, fs) == True{} : Bool}
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, up, subs, path, bs,
      [wk.rest(nm, hlp, req, dflt)], False{}, seen})
    == Shake.St{Shake.Free{}, args, up, subs, path, wk.pushed(fs, nm, bs), [wk.rest(nm, hlp, req, dflt)], False{},
      wk.seen(fs, seen)} : Shake.St}

def wk.walk_plain(fs, args, up, subs, path, bs, nm, hlp, req, dflt, seen, hp, hu):
  match fs:
    case Nil{}:
      {==}
    case Con{+ww, +tl}:
      +pl = wk.and_l(plain_word(ww), all_plain(tl), hp)
      su = wk.and_l(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), wk.unfound(subs, tl), hu)
      e = Equal.sym(Shake.St,
        Shake.parse.step(ww, Shake.St{Shake.Free{}, args, up, subs, path, bs,
            [wk.rest(nm, hlp, req, dflt)], False{}, seen}),
        Shake.parse.take_pos(ww, args, up, subs, path, bs, [wk.rest(nm, hlp, req, dflt)], False{}),
        wk.word_step(ww, args, up, subs, path, bs, [wk.rest(nm, hlp, req, dflt)], seen, wk.plain_dd(ww, pl),
          wk.plain_help(ww, pl), wk.plain_dash(ww, pl), wk.none_of(Shake.find_sub(subs, ww), su)))
      %e : {Shake.parse.walk(tl, _)
        == Shake.St{Shake.Free{}, args, up, subs, path, wk.pushed(tl, nm, Shake.Bind{nm, ww} <> bs),
          [wk.rest(nm, hlp, req, dflt)], False{}, wk.seen(tl, True{})} : Shake.St}
      wk.walk_plain(tl, args, up, subs, path, Shake.Bind{nm, ww} <> bs, nm, hlp, req, dflt, True{},
        wk.and_r(plain_word(ww), all_plain(tl), hp),
        wk.and_r(Maybe.is_none(&2, Shake.Sub, Shake.find_sub(subs, ww)), wk.unfound(subs, tl), hu))

# after `--`, every word binds the rest positional once more
law wk.walk_raw:
  for fs: List<&2, String>
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for bs: List<&2, Shake.Bind>
  for +nm: String
  for +hlp: String
  for +req: Bool
  for +dflt: Maybe<&2, String>
  for seen: Bool
  {Shake.parse.walk(fs, Shake.St{Shake.Free{}, args, up, subs, path, bs,
      [wk.rest(nm, hlp, req, dflt)], True{}, seen})
    == Shake.St{Shake.Free{}, args, up, subs, path, wk.pushed(fs, nm, bs), [wk.rest(nm, hlp, req, dflt)], True{},
      wk.seen(fs, seen)} : Shake.St}

def wk.walk_raw(fs, args, up, subs, path, bs, nm, hlp, req, dflt, _seen):
  match fs:
    case Nil{}:
      {==}
    case Con{ww, tl}:
      wk.walk_raw(tl, args, up, subs, path, Shake.Bind{nm, ww} <> bs, nm, hlp, req, dflt, True{})
