# shake/grow: a walker only ever puts bindings in front of those it holds.
# Every arm of `step` either keeps the bindings or puts one in front, and a
# cluster does so letter by letter, so a binding made at one word is still
# there, behind the later ones, when the words end. This is the invariant of
# docs/rfc/shake-walker-proofs.md (WP2), shaped like bolt's `extends`.
import Base
import ./cli.bend as Shake

# the bindings a walker holds
def binds_of(st: Shake.St) -> List<&2, Shake.Bind>:
  Shake.St{_m, _a, _g, _s, _p, bb, _o, _r, _n} = st
  bb

# `big` is `small` with some bindings put in front
def gw.Ext(big: List<&2, Shake.Bind>, small: List<&2, Shake.Bind>) -> Type:
  &xs: List<&2, Shake.Bind> -> {big == List.append(&2, Shake.Bind, xs, small) : List<&2, Shake.Bind>}

# appending bindings is associative
law gw.app:
  for +aa: List<&2, Shake.Bind>
  for +bb: List<&2, Shake.Bind>
  for +cc: List<&2, Shake.Bind>
  {List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, aa, bb), cc)
    == List.append(&2, Shake.Bind, aa, List.append(&2, Shake.Bind, bb, cc)) : List<&2, Shake.Bind>}

def gw.app(aa, bb, cc):
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, Shake.Bind>, List<&2, Shake.Bind>, xs => hh <> xs,
        List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, tt, bb), cc),
        List.append(&2, Shake.Bind, tt, List.append(&2, Shake.Bind, bb, cc)), gw.app(tt, bb, cc))

# bindings in front of bindings in front of a list are bindings in front of it
law gw.chain:
  for +env: List<&2, Shake.Bind>
  for +env1: List<&2, Shake.Bind>
  for +env2: List<&2, Shake.Bind>
  for w1: gw.Ext(env1, env)
  for w2: gw.Ext(env2, env1)
  gw.Ext(env2, env)

def gw.chain(env, env1, env2, w1, w2):
  (x1, e1) = w1
  (x2, e2) = w2
  +aa = {x1 : List<&2, Shake.Bind>}
  +bb = {x2 : List<&2, Shake.Bind>}
  (List.append(&2, Shake.Bind, bb, aa),
    Equal.trans(List<&2, Shake.Bind>, env2, List.append(&2, Shake.Bind, bb, env1),
      List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, bb, aa), env), e2,
      Equal.trans(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, bb, env1),
        List.append(&2, Shake.Bind, bb, List.append(&2, Shake.Bind, aa, env)),
        List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, bb, aa), env),
        Equal.cong(List<&2, Shake.Bind>, List<&2, Shake.Bind>, yy => List.append(&2, Shake.Bind, bb, yy),
          env1, List.append(&2, Shake.Bind, aa, env), e1),
        Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, bb, aa), env),
          List.append(&2, Shake.Bind, bb, List.append(&2, Shake.Bind, aa, env)), gw.app(bb, aa, env)))))

# no binding in front
law gw.same:
  for +env: List<&2, Shake.Bind>
  gw.Ext(env, env)

def gw.same(_env):
  ([], {==})

# one binding in front
law gw.one:
  for +bb: Shake.Bind
  for +env: List<&2, Shake.Bind>
  gw.Ext(bb <> env, env)

def gw.one(bb, _env):
  ([bb], {==})

# a checked value binds or fails
law gw.choice:
  for ok: Bool
  for +name: String
  for +val: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_choice(ok, name, val, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.choice(ok, name, val, _args, _specs, _subs, _path, binds, _pos, _raw, _seen):
  match ok:
    case True{}:
      gw.one(Shake.Bind{name, val}, binds)
    case False{}:
      gw.same(binds)

# an option's value binds or fails
law gw.opt_val:
  for +name: String
  for +val: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_opt_val(name, val, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.opt_val(name, val, args, specs, subs, path, binds, pos, raw, seen):
  gw.choice(Shake.allowed(Shake.parse.choices(Shake.by_name(args, name)), val), name, val, args, specs, subs,
    path, binds, pos, raw, seen)

# a flag binds, or fails on a glued value
law gw.flag:
  for val: Maybe<&2, String>
  for +name: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_flag(val, name, orig, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.flag(val, name, _orig, _args, _specs, _subs, _path, binds, _pos, _raw, _seen):
  match val:
    case None{}:
      gw.one(Shake.Bind{name, "true"}, binds)
    case Some{_vv}:
      gw.same(binds)

# an option binds its glued value, or waits for the next word
law gw.opt:
  for val: Maybe<&2, String>
  for +name: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_opt(val, name, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.opt(val, name, args, specs, subs, path, binds, pos, raw, seen):
  match val:
    case None{}:
      gw.same(binds)
    case Some{vv}:
      gw.opt_val(name, vv, args, specs, subs, path, binds, pos, raw, seen)

# the once-check keeps the bindings of the walker it is given
law gw.once:
  for again: Bool
  for st: Shake.St
  for +name: String
  for +path: List<&2, String>
  for +bs: List<&2, Shake.Bind>
  gw.Ext(binds_of(st), bs) -> gw.Ext(binds_of(Shake.parse.once(again, st, name, path)), bs)

def gw.once(again, st, _name, _path, _bs):
  match again:
    case True{}:
      match st:
        case Shake.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
          ww => ww
    case False{}:
      ww => ww

# a found argument, by its kind
law gw.kind:
  for kk: Shake.ArgKind
  for +name: String
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_arg.kind(kk, name, val, orig, args, specs, subs, path, binds, pos, raw, seen)),
    binds)

def gw.kind(kk, name, val, orig, args, specs, subs, path, binds, pos, raw, seen):
  match kk:
    case Shake.Flag{}:
      gw.once(Shake.bound(binds, name), Shake.parse.take_flag(val, name, orig, args, specs, subs, path, binds,
          pos, raw, seen), name, path, binds)(
        gw.flag(val, name, orig, args, specs, subs, path, binds, pos, raw, seen))
    case Shake.Opt{}:
      gw.once(Shake.bound(binds, name), Shake.parse.take_opt(val, name, args, specs, subs, path, binds, pos,
          raw, seen), name, path, binds)(
        gw.opt(val, name, args, specs, subs, path, binds, pos, raw, seen))
    case Shake.Many{}:
      gw.opt(val, name, args, specs, subs, path, binds, pos, raw, seen)
    case Shake.Pos{}:
      gw.same(binds)
    case Shake.Rest{}:
      gw.same(binds)

# a found argument, or an unknown flag
law gw.arg:
  for found: Maybe<&2, Shake.Arg>
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_arg(found, val, orig, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.arg(found, val, orig, args, specs, subs, path, binds, pos, raw, seen):
  match found:
    case None{}:
      gw.same(binds)
    case Some{aa}:
      match aa:
        case Shake.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          gw.kind(kind, name, val, orig, args, specs, subs, path, binds, pos, raw, seen)

# a long option with a name, or `--=...`
law gw.named:
  for empty: Bool
  for +name: String
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_long.named(empty, name, val, orig, args, specs, subs, path, binds, pos, raw,
    seen)), binds)

def gw.named(empty, name, val, orig, args, specs, subs, path, binds, pos, raw, seen):
  match empty:
    case True{}:
      gw.same(binds)
    case False{}:
      gw.arg(Shake.by_long(args, name), val, orig, args, specs, subs, path, binds, pos, raw, seen)

# a long option after the `=` cut
law gw.cut:
  for nv: String & Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_long.cut(nv, orig, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.cut(nv, orig, args, specs, subs, path, binds, pos, raw, seen):
  match nv:
    case (+name, val):
      gw.named(String.is_empty(name), name, val, orig, args, specs, subs, path, binds, pos, raw, seen)

# a long option
law gw.long:
  for +body: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_long(body, orig, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.long(body, orig, args, specs, subs, path, binds, pos, raw, seen):
  gw.cut(Shake.cut_eq(body), orig, args, specs, subs, path, binds, pos, raw, seen)

# one letter of a cluster, read
law gw.apply:
  for st: Shake.St
  for +cc: Char
  for +rest: String
  for +orig: String
  gw.Ext(binds_of(Shake.cluster.apply(st, cc, rest, orig)), binds_of(st))

def gw.apply(st, cc, rest, orig):
  match st:
    case Shake.St{_m, +args, +specs, +subs, +path, +binds, +pos, +raw, +seen}:
      gw.arg(Shake.by_short(args, SCon{cc, SNil{}}), Shake.cluster.val(Shake.by_short(args, SCon{cc, SNil{}}), rest),
        orig, args, specs, subs, path, binds, pos, raw, seen)

# one letter of a cluster, unless an earlier one ended it
law gw.letter:
  for done: Bool
  for +cc: Char
  for +rest: String
  for +orig: String
  for +st: Shake.St
  gw.Ext(binds_of(Shake.cluster.letter(done, cc, rest, orig, st)), binds_of(st))

def gw.letter(done, cc, rest, orig, st):
  match done:
    case True{}:
      gw.same(binds_of(st))
    case False{}:
      gw.apply(st, cc, rest, orig)

# every letter of a cluster
law gw.cluster:
  for body: String
  for +orig: String
  for +st: Shake.St
  for +done: Bool
  gw.Ext(binds_of(Shake.cluster(body, orig, st, done)), binds_of(st))

def gw.cluster(body, orig, st, done):
  match body:
    case SNil{}:
      gw.same(binds_of(st))
    case SCon{+cc, +rest}:
      +next = Shake.cluster.letter(done, cc, rest, orig, st)
      gw.chain(binds_of(st), binds_of(next),
        binds_of(Shake.cluster(rest, orig, next, Shake.cluster.done(done, cc, rest, st))),
        gw.letter(done, cc, rest, orig, st),
        gw.cluster(rest, orig, next, Shake.cluster.done(done, cc, rest, st)))

# a short option word
law gw.short:
  for +body: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.take_short(body, orig, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.short(body, orig, args, specs, subs, path, binds, pos, raw, seen):
  gw.cluster(body, orig, Shake.St{Shake.Free{}, args, specs, subs, path, binds, pos, raw, seen}, False{})

# a plain word bound to the next positional, or refused
law gw.pos:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for pos: List<&2, Shake.Arg>
  for +raw: Bool
  gw.Ext(binds_of(Shake.parse.take_pos(tok, args, specs, subs, path, binds, pos, raw)), binds)

def gw.pos(tok, args, specs, subs, path, binds, pos, raw):
  match pos:
    case Nil{}:
      gw.same(binds)
    case Con{hh, tt}:
      match hh:
        case Shake.Arg{+name, +sh, +lo, +kind, +hp, +req, +dflt, +cs}:
          gw.choice(Shake.allowed(cs, tok), name, tok, args, specs, subs, path, binds,
            Shake.parse.take_pos.keep(Shake.rest.is(Shake.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
              Shake.Arg{name, sh, lo, kind, hp, req, dflt, cs}, tt), raw, True{})

# entering a subcommand keeps the bindings
law gw.enter:
  for ss: Shake.Sub
  for +specs: List<&2, Shake.Arg>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  gw.Ext(binds_of(Shake.parse.enter(ss, specs, path, binds)), binds)

def gw.enter(ss, _specs, _path, binds):
  match ss:
    case Shake.Sub{_n, _a, _g, _c}:
      gw.same(binds)

# a subcommand entered, or a required positional missing
law gw.enter_or:
  for miss: Maybe<&2, String>
  for ss: Shake.Sub
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.enter_or(miss, ss, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.enter_or(miss, ss, _args, specs, _subs, path, binds, _pos, _raw, _seen):
  match miss:
    case None{}:
      gw.enter(ss, specs, path, binds)
    case Some{_n}:
      gw.same(binds)

# a found subcommand, or a positional
law gw.word_go:
  for found: Maybe<&2, Shake.Sub>
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.word.go(found, tok, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.word_go(found, tok, args, specs, subs, path, binds, pos, raw, seen):
  match found:
    case None{}:
      gw.pos(tok, args, specs, subs, path, binds, pos, raw)
    case Some{ss}:
      gw.enter_or(Shake.parse.first_req(pos), ss, args, specs, subs, path, binds, pos, raw, seen)

# a plain word
law gw.word:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.word(tok, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.word(tok, args, specs, subs, path, binds, pos, raw, seen):
  gw.word_go(Shake.find_sub(subs, tok), tok, args, specs, subs, path, binds, pos, raw, seen)

# `-` as a word, or a short option
law gw.short_go:
  for alone: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.short.go(alone, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.short_go(alone, tok, args, specs, subs, path, binds, pos, seen):
  match alone:
    case True{}:
      gw.word(tok, args, specs, subs, path, binds, pos, False{}, seen)
    case False{}:
      gw.short(String.drop(tok, 1n), tok, args, specs, subs, path, binds, pos, False{}, seen)

# a word that starts with `-`, or not
law gw.step_short:
  for dash: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.short(dash, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.step_short(dash, tok, args, specs, subs, path, binds, pos, seen):
  match dash:
    case True{}:
      gw.short_go(String.eq(tok, "-"), tok, args, specs, subs, path, binds, pos, seen)
    case False{}:
      gw.word(tok, args, specs, subs, path, binds, pos, False{}, seen)

# a long option, a short option, or a word
law gw.kind_go:
  for long: Bool
  for +dash: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.kind.go(long, dash, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.kind_go(long, dash, tok, args, specs, subs, path, binds, pos, seen):
  match long:
    case True{}:
      gw.long(String.drop(tok, 2n), tok, args, specs, subs, path, binds, pos, False{}, seen)
    case False{}:
      gw.step_short(dash, tok, args, specs, subs, path, binds, pos, seen)

# `help`, or any other word
law gw.help:
  for hit: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.help(hit, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.help(hit, tok, args, specs, subs, path, binds, pos, seen):
  match hit:
    case True{}:
      gw.same(binds)
    case False{}:
      gw.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, specs, subs, path, binds,
        pos, seen)

# `--`, or any other word
law gw.end:
  for end: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.end(end, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.end(end, tok, args, specs, subs, path, binds, pos, seen):
  match end:
    case True{}:
      gw.same(binds)
    case False{}:
      gw.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, specs, subs, path, binds, pos, seen)

# a free walker, before or after `--`
law gw.raw:
  for raw: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.raw(raw, tok, args, specs, subs, path, binds, pos, seen)), binds)

def gw.raw(raw, tok, args, specs, subs, path, binds, pos, seen):
  match raw:
    case True{}:
      gw.pos(tok, args, specs, subs, path, binds, pos, True{})
    case False{}:
      gw.end(String.eq(tok, "--"), tok, args, specs, subs, path, binds, pos, seen)

# an option's value, or a flag-shaped word where it was wanted
law gw.need:
  for flag: Bool
  for +name: String
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.need(flag, name, tok, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.need(flag, name, tok, args, specs, subs, path, binds, pos, raw, seen):
  match flag:
    case True{}:
      gw.same(binds)
    case False{}:
      gw.opt_val(name, tok, args, specs, subs, path, binds, pos, raw, seen)

# a word after `help`
law gw.help_path:
  for found: Maybe<&2, Shake.Sub>
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.help_path(found, tok, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.help_path(found, _tok, _args, _specs, _subs, _path, binds, _pos, _raw, _seen):
  match found:
    case None{}:
      gw.same(binds)
    case Some{ss}:
      match ss:
        case Shake.Sub{_n, _a, _g, _c}:
          gw.same(binds)

# one word, in each mode
law gw.mode:
  for mode: Shake.Mode
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +specs: List<&2, Shake.Arg>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Ext(binds_of(Shake.parse.step.mode(mode, tok, args, specs, subs, path, binds, pos, raw, seen)), binds)

def gw.mode(mode, tok, args, specs, subs, path, binds, pos, raw, seen):
  match mode:
    case Shake.Dead{_e}:
      gw.same(binds)
    case Shake.Need{name}:
      gw.need(Shake.looks_flag(tok), name, tok, args, specs, subs, path, binds, pos, raw, seen)
    case Shake.Help{}:
      gw.help_path(Shake.find_sub(subs, tok), tok, args, specs, subs, path, binds, pos, raw, seen)
    case Shake.Free{}:
      gw.raw(raw, tok, args, specs, subs, path, binds, pos, seen)

# one word puts at most one binding in front, or, for a cluster, one per
# letter
law gw.step:
  for +tok: String
  for st: Shake.St
  gw.Ext(binds_of(Shake.parse.step(tok, st)), binds_of(st))

def gw.step(tok, st):
  match st:
    case Shake.St{mode, +args, +specs, +subs, +path, +binds, +pos, +raw, +seen}:
      gw.mode(mode, tok, args, specs, subs, path, binds, pos, raw, seen)

# LAW: whatever words it reads, a walker's bindings are the ones it held with
# some put in front: none is ever dropped or replaced
law binds_grow:
  for more: List<&2, String>
  for +st: Shake.St
  gw.Ext(binds_of(Shake.parse.walk(more, st)), binds_of(st))

# by induction on the words: each step puts some in front, and so does the
# walk after it
def binds_grow(more, st):
  match more:
    case Nil{}:
      gw.same(binds_of(st))
    case Con{+hh, +tt}:
      gw.chain(binds_of(st), binds_of(Shake.parse.step(hh, st)),
        binds_of(Shake.parse.walk(tt, Shake.parse.step(hh, st))), gw.step(hh, st),
        binds_grow(tt, Shake.parse.step(hh, st)))

# a default goes in front, or not at all
law gw.fill_one:
  for skip: Bool
  for +name: String
  for +val: String
  for +rest: List<&2, Shake.Bind>
  gw.Ext(Shake.fill.one(skip, name, val, rest), rest)

def gw.fill_one(skip, name, val, rest):
  match skip:
    case True{}:
      gw.same(rest)
    case False{}:
      gw.one(Shake.Bind{name, val}, rest)

# an argument with a default, or none
law gw.fill_go:
  for dd: Maybe<&2, String>
  for +name: String
  for +binds: List<&2, Shake.Bind>
  gw.Ext(Shake.fill.arg.go(dd, name, binds), binds)

def gw.fill_go(dd, name, binds):
  match dd:
    case None{}:
      gw.same(binds)
    case Some{vv}:
      gw.fill_one(Shake.bound(binds, name), name, vv, binds)

# one argument's default
law gw.fill_arg:
  for aa: Shake.Arg
  for +binds: List<&2, Shake.Bind>
  gw.Ext(Shake.fill.arg(aa, binds), binds)

def gw.fill_arg(aa, binds):
  match aa:
    case Shake.Arg{+name, _s, _l, _k, _h, _r, dflt, _c}:
      gw.fill_go(dflt, name, binds)

# LAW: filling defaults only puts bindings in front
law gw.fill:
  for args: List<&2, Shake.Arg>
  for +binds: List<&2, Shake.Bind>
  gw.Ext(Shake.fill.args(args, binds), binds)

def gw.fill(args, binds):
  match args:
    case Nil{}:
      gw.same(binds)
    case Con{+hh, +tt}:
      gw.chain(binds, Shake.fill.args(tt, binds), Shake.fill.arg(hh, Shake.fill.args(tt, binds)),
        gw.fill(tt, binds), gw.fill_arg(hh, Shake.fill.args(tt, binds)))

# the values `get_all` reads from a result, none for a failure
def gw.all_of(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>, +name: String) -> List<&2, String>:
  match rr:
    case Done{mm}:
      Shake.get_all(mm, name)
    case Fail{_e}:
      []

# Unit for a failure, Empty for a success: a motive that tells them apart
def gw.fail_ty(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> Type:
  match rr:
    case Done{_m}:
      Empty
    case Fail{_e}:
      Unit

# a failure is never a success
law gw.fail_done:
  for +err: Shake.ParseErr
  for +found: Shake.Matched
  for hh: {Fail{err} == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  Empty

def gw.fail_done(_err, _found, hh):
  %hh : gw.fail_ty(_)
  Unit{}

# a success after the required check reads the bindings it was given,
# reversed
law gw.miss_done:
  for mm: Maybe<&2, String>
  for +path: List<&2, String>
  for +fb: List<&2, Shake.Bind>
  for +found: Shake.Matched
  for +name: String
  for hh: {Shake.parse.finish.miss(mm, path, fb) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {Shake.get_all(found, name) == Shake.get_all.bind(List.reverse(&2, Shake.Bind, fb), name) : List<&2, String>}

def gw.miss_done(mm, path, fb, found, name, hh):
  match mm:
    case Some{nn}:
      Empty.absurd({Shake.get_all(found, name) == Shake.get_all.bind(List.reverse(&2, Shake.Bind, fb), name)
          : List<&2, String>},
        gw.fail_done(Shake.Missing{path, nn}, found, hh))
    case None{}:
      Equal.sym(List<&2, String>, Shake.get_all.bind(List.reverse(&2, Shake.Bind, fb), name),
        Shake.get_all(found, name),
        Equal.cong(Result<&2, &2, Shake.ParseErr, Shake.Matched>, List<&2, String>, rr => gw.all_of(rr, name),
          Done{Shake.Matched{path, List.reverse(&2, Shake.Bind, fb)}}, Done{found}, hh))

# what `gw.finished` claims of a walker holding `binds`
def gw.finished.ty(+found: Shake.Matched, +name: String, +binds: List<&2, Shake.Bind>) -> Type:
  &defs: List<&2, Shake.Bind> -> {Shake.get_all(found, name)
    == Shake.get_all.bind(List.reverse(&2, Shake.Bind, List.append(&2, Shake.Bind, defs, binds)), name)
    : List<&2, String>}

# a free walker's success, once filling its defaults is known to put them in
# front
law gw.finished.free:
  for +specs: List<&2, Shake.Arg>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +found: Shake.Matched
  for +name: String
  for hh: {Shake.parse.finish.ok(specs, path, Shake.fill.args(specs, binds)) == Done{found}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for ww: gw.Ext(Shake.fill.args(specs, binds), binds)
  gw.finished.ty(found, name, binds)

def gw.finished.free(specs, path, binds, found, name, hh, ww):
  (dx, ee) = ww
  +defs = {dx : List<&2, Shake.Bind>}
  (defs, Equal.trans(List<&2, String>, Shake.get_all(found, name),
    Shake.get_all.bind(List.reverse(&2, Shake.Bind, Shake.fill.args(specs, binds)), name),
    Shake.get_all.bind(List.reverse(&2, Shake.Bind, List.append(&2, Shake.Bind, defs, binds)), name),
    gw.miss_done(Shake.miss.args(specs, Shake.fill.args(specs, binds)), path, Shake.fill.args(specs, binds),
      found, name, hh),
    Equal.cong(List<&2, Shake.Bind>, List<&2, String>,
      xs => Shake.get_all.bind(List.reverse(&2, Shake.Bind, xs), name),
      Shake.fill.args(specs, binds), List.append(&2, Shake.Bind, defs, binds), ee)))

# LAW: a walker that finishes as a success reads its bindings, with defaults
# put in front, reversed
law gw.finished:
  for fs: Shake.St
  for +found: Shake.Matched
  for +name: String
  for hh: {Shake.parse.finish(fs) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  exs defs: List<&2, Shake.Bind>
  {Shake.get_all(found, name)
    == Shake.get_all.bind(List.reverse(&2, Shake.Bind, List.append(&2, Shake.Bind, defs, binds_of(fs))), name)
    : List<&2, String>}

def gw.finished(fs, found, name, hh):
  match fs:
    case Shake.St{Shake.Free{}, _a, +specs, _s, +path, +binds, _o, _r, _n}:
      gw.finished.free(specs, path, binds, found, name, hh, gw.fill(specs, binds))
    case Shake.St{Shake.Dead{+ee}, _a, _g, _s, _p, +binds, _o, _r, _n}:
      Empty.absurd(gw.finished.ty(found, name, binds), gw.fail_done(ee, found, hh))
    case Shake.St{Shake.Need{+nn}, _a, _g, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd(gw.finished.ty(found, name, binds), gw.fail_done(Shake.NoValue{path, nn}, found, hh))
    case Shake.St{Shake.Help{}, _a, _g, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd(gw.finished.ty(found, name, binds), gw.fail_done(Shake.NeedHelp{path}, found, hh))

# reversing onto a list is reversing, then appending it
law gw.rev_go:
  for xs: List<&2, Shake.Bind>
  for +acc: List<&2, Shake.Bind>
  {List.reverse.go(&2, Shake.Bind, xs, acc)
    == List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, xs, []), acc) : List<&2, Shake.Bind>}

def gw.rev_go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, tt, hh <> acc),
        List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, []), hh <> acc),
        List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, [hh]), acc),
        gw.rev_go(tt, hh <> acc),
        Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, [hh]), acc),
          List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, []), hh <> acc),
          Equal.trans(List<&2, Shake.Bind>,
            List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, [hh]), acc),
            List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, []), [hh]),
              acc),
            List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, []), hh <> acc),
            Equal.cong(List<&2, Shake.Bind>, List<&2, Shake.Bind>, ys => List.append(&2, Shake.Bind, ys, acc),
              List.reverse.go(&2, Shake.Bind, tt, [hh]),
              List.append(&2, Shake.Bind, List.reverse.go(&2, Shake.Bind, tt, []), [hh]), gw.rev_go(tt, [hh])),
            gw.app(List.reverse.go(&2, Shake.Bind, tt, []), [hh], acc))))

# reversing two lists one after the other onto a list
law gw.rev_app:
  for xs: List<&2, Shake.Bind>
  for +ys: List<&2, Shake.Bind>
  for +acc: List<&2, Shake.Bind>
  {List.reverse.go(&2, Shake.Bind, List.append(&2, Shake.Bind, xs, ys), acc)
    == List.reverse.go(&2, Shake.Bind, ys, List.reverse.go(&2, Shake.Bind, xs, acc)) : List<&2, Shake.Bind>}

def gw.rev_app(xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      gw.rev_app(tt, ys, hh <> acc)

# LAW: the bindings of a finished walk, reversed, with bindings `xs` made
# along the way: those held before them, reversed, then `xs` reversed, then
# the rest
law gw.rev_split:
  for +defs: List<&2, Shake.Bind>
  for +new: List<&2, Shake.Bind>
  for +xs: List<&2, Shake.Bind>
  for +bs: List<&2, Shake.Bind>
  {List.reverse(&2, Shake.Bind,
      List.append(&2, Shake.Bind, defs, List.append(&2, Shake.Bind, new, List.append(&2, Shake.Bind, xs, bs))))
    == List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs),
      List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs),
        List.reverse.go(&2, Shake.Bind, new, List.reverse(&2, Shake.Bind, defs)))) : List<&2, Shake.Bind>}

def gw.rev_split(defs, new, xs, bs):
  +r0 = List.reverse(&2, Shake.Bind, defs)
  +r1 = List.reverse.go(&2, Shake.Bind, new, r0)
  +y1 = List.append(&2, Shake.Bind, xs, bs)
  +y0 = List.append(&2, Shake.Bind, new, y1)
  Equal.trans(List<&2, Shake.Bind>, List.reverse(&2, Shake.Bind, List.append(&2, Shake.Bind, defs, y0)),
    List.reverse.go(&2, Shake.Bind, y0, r0),
    List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs),
      List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs), r1)),
    gw.rev_app(defs, y0, []),
    Equal.trans(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, y0, r0), List.reverse.go(&2, Shake.Bind, y1, r1),
      List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs),
        List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs), r1)),
      gw.rev_app(new, y1, r0),
      Equal.trans(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, y1, r1),
        List.reverse.go(&2, Shake.Bind, bs, List.reverse.go(&2, Shake.Bind, xs, r1)),
        List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs),
          List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs), r1)),
        gw.rev_app(xs, bs, r1),
        Equal.trans(List<&2, Shake.Bind>, List.reverse.go(&2, Shake.Bind, bs, List.reverse.go(&2, Shake.Bind, xs, r1)),
          List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs), List.reverse.go(&2, Shake.Bind, xs, r1)),
          List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs),
            List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs), r1)),
          gw.rev_go(bs, List.reverse.go(&2, Shake.Bind, xs, r1)),
          Equal.cong(List<&2, Shake.Bind>, List<&2, Shake.Bind>,
            zs => List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, bs), zs),
            List.reverse.go(&2, Shake.Bind, xs, r1), List.append(&2, Shake.Bind, List.reverse(&2, Shake.Bind, xs), r1),
            gw.rev_go(xs, r1))))))
