# shake/grow: what a word can do to the walker, and so what a walk keeps.
# Every word either stays in the current command, putting bindings in front of
# its own, or enters a subcommand, leaving the current command's arguments and
# bindings above it, or leaves the walker stuck in help or failed. So a
# binding made in a command is still that command's, behind the later ones,
# when the words end, and a successful parse reads it from that command's
# Matched. This is the invariant of docs/rfc/shake-walker-proofs.md (WP2),
# shaped like bolt's `extends`.
import Base
import ./cli.bend as Shake
import ./eq.bend as Eq

# the bindings a walker holds for its current command
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
law gw.esame:
  for +env: List<&2, Shake.Bind>
  gw.Ext(env, env)

def gw.esame(_env):
  ([], {==})

# one binding in front
law gw.eone:
  for +bb: Shake.Bind
  for +env: List<&2, Shake.Bind>
  gw.Ext(bb <> env, env)

def gw.eone(bb, _env):
  ([bb], {==})


# what a word can change in the walker that a result reads: the current
# command's arguments, the commands above it, the selected path and the
# current command's bindings
type View is Data:
  View{args: List<&2, Shake.Arg>, up: List<&2, Shake.Level>, path: List<&2, String>, binds: List<&2, Shake.Bind>}

# a walker's view
def view(st: Shake.St) -> View:
  Shake.St{_m, args, up, _s, path, binds, _o, _r, _n} = st
  View{args, up, path, binds}

# a view with bindings put in front of the current command's
def gw.put(xs: List<&2, Shake.Bind>, vv: View) -> View:
  View{args, up, path, binds} = vv
  View{args, up, path, List.append(&2, Shake.Bind, xs, binds)}

# a view that is `small` with some bindings put in front
def gw.VStay(big: View, small: View) -> Type:
  &xs: List<&2, Shake.Bind> -> {big == gw.put(xs, small) : View}

# a walker that stayed in the command of `small`, some bindings in front
def gw.Stay(big: Shake.St, small: View) -> Type:
  gw.VStay(view(big), small)

# a view's selected path
def gw.vpath(vv: View) -> List<&2, String>:
  View{_a, _u, path, _b} = vv
  path

# bindings put in front twice are put in front once
law gw.put_put:
  for +bb: List<&2, Shake.Bind>
  for +aa: List<&2, Shake.Bind>
  for vv: View
  {gw.put(bb, gw.put(aa, vv)) == gw.put(List.append(&2, Shake.Bind, bb, aa), vv) : View}

def gw.put_put(bb, aa, vv):
  match vv:
    case View{+args, +up, +path, +binds}:
      Equal.cong(List<&2, Shake.Bind>, View, xs => View{args, up, path, xs},
        List.append(&2, Shake.Bind, bb, List.append(&2, Shake.Bind, aa, binds)),
        List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, bb, aa), binds),
        Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, bb, aa), binds),
          List.append(&2, Shake.Bind, bb, List.append(&2, Shake.Bind, aa, binds)), gw.app(bb, aa, binds)))

# a walker stays where it is
law gw.same_st:
  for st: Shake.St
  gw.Stay(st, view(st))

def gw.same_st(st):
  match st:
    case Shake.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      ([], {==})

# staying twice is staying
law gw.stay_chain:
  for +v0: View
  for +st1: Shake.St
  for +st2: Shake.St
  for w1: gw.Stay(st1, v0)
  for w2: gw.Stay(st2, view(st1))
  gw.Stay(st2, v0)

def gw.stay_chain(v0, st1, st2, w1, w2):
  (x1, e1) = w1
  (x2, e2) = w2
  +aa = {x1 : List<&2, Shake.Bind>}
  +bb = {x2 : List<&2, Shake.Bind>}
  (List.append(&2, Shake.Bind, bb, aa),
    Equal.trans(View, view(st2), gw.put(bb, view(st1)), gw.put(List.append(&2, Shake.Bind, bb, aa), v0), e2,
      Equal.trans(View, gw.put(bb, view(st1)), gw.put(bb, gw.put(aa, v0)),
        gw.put(List.append(&2, Shake.Bind, bb, aa), v0),
        Equal.cong(View, View, vv => gw.put(bb, vv), view(st1), gw.put(aa, v0), e1),
        gw.put_put(bb, aa, v0))))

# a view with its path replaced
def gw.repath(vv: View, +path: List<&2, String>) -> View:
  View{args, up, _p, binds} = vv
  View{args, up, path, binds}

# replacing a view's path with the one it has changes nothing
law gw.repath_put:
  for +xs: List<&2, Shake.Bind>
  for vv: View
  for +path: List<&2, String>
  for h_path: {gw.vpath(vv) == path : List<&2, String>}
  {gw.repath(gw.put(xs, vv), path) == gw.put(xs, vv) : View}

def gw.repath_put(xs, vv, path, h_path):
  match vv:
    case View{+args, +up, +pp, +binds}:
      Equal.cong(List<&2, String>, View, qq => View{args, up, qq, List.append(&2, Shake.Bind, xs, binds)}, path, pp,
        Equal.sym(List<&2, String>, pp, path, h_path))

# the once-check's failure keeps the view, with the path it is told, which is
# the walker's own
law gw.once.dead:
  for +aa: List<&2, Shake.Arg>
  for +gg: List<&2, Shake.Level>
  for +pp: List<&2, String>
  for +bb: List<&2, Shake.Bind>
  for +path: List<&2, String>
  for +vv: View
  for h_path: {gw.vpath(vv) == path : List<&2, String>}
  for ww: gw.VStay(View{aa, gg, pp, bb}, vv)
  gw.VStay(View{aa, gg, path, bb}, vv)

def gw.once.dead(aa, gg, pp, bb, path, vv, h_path, ww):
  (x1, e1) = ww
  +xs = {x1 : List<&2, Shake.Bind>}
  (xs, Equal.trans(View, View{aa, gg, path, bb}, gw.repath(gw.put(xs, vv), path), gw.put(xs, vv),
    Equal.cong(View, View, v2 => gw.repath(v2, path), View{aa, gg, pp, bb}, gw.put(xs, vv), e1),
    gw.repath_put(xs, vv, path, h_path)))

law gw.choice:
  for ok: Bool
  for +name: String
  for +val: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), View{args, up,
      path, binds})

def gw.choice(ok, name, val, _args, _up, _subs, _path, _binds, _pos, _raw, _seen):
  match ok:
    case True{}:
      ([Shake.Bind{name, val}], {==})
    case False{}:
      ([], {==})

# an option's value binds or fails
law gw.opt_val:
  for +name: String
  for +val: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.opt_val(name, val, args, up, subs, path, binds, pos, raw, seen):
  gw.choice(Shake.allowed(Shake.parse.choices(Shake.by_name(args, name)), val), name, val, args, up, subs,
    path, binds, pos, raw, seen)

# a flag binds, or fails on a glued value
law gw.flag:
  for val: Maybe<&2, String>
  for +name: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), View{args, up,
      path, binds})

def gw.flag(val, name, _orig, _args, _up, _subs, _path, _binds, _pos, _raw, _seen):
  match val:
    case None{}:
      ([Shake.Bind{name, "true"}], {==})
    case Some{_vv}:
      ([], {==})

# an option binds its glued value, or waits for the next word
law gw.opt:
  for val: Maybe<&2, String>
  for +name: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.opt(val, name, args, up, subs, path, binds, pos, raw, seen):
  match val:
    case None{}:
      ([], {==})
    case Some{vv}:
      gw.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen)

# the once-check keeps the bindings of the walker it is given
law gw.once:
  for again: Bool
  for st: Shake.St
  for +name: String
  for +path: List<&2, String>
  for +vv: View
  for +h_path: {gw.vpath(vv) == path : List<&2, String>}
  gw.Stay(st, vv) -> gw.Stay(Shake.parse.once(again, st, name, path), vv)

def gw.once(again, st, _name, path, vv, h_path):
  match again:
    case True{}:
      match st:
        case Shake.St{_m, +aa, +gg, _s, +pp, +bb, _o, _r, _n}:
          ww => gw.once.dead(aa, gg, pp, bb, path, vv, h_path, ww)
    case False{}:
      ww => ww

# a found argument, by its kind
law gw.kind:
  for kk: Shake.ArgKind
  for +name: String
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen),
      View{args, up, path, binds})

def gw.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen):
  match kk:
    case Shake.Flag{}:
      gw.once(Shake.bound(binds, name), Shake.parse.take_flag(val, name, orig, args, up, subs, path, binds,
          pos, raw, seen), name, path, View{args, up, path, binds}, {==})(
        gw.flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen))
    case Shake.Opt{}:
      gw.once(Shake.bound(binds, name), Shake.parse.take_opt(val, name, args, up, subs, path, binds, pos,
          raw, seen), name, path, View{args, up, path, binds}, {==})(
        gw.opt(val, name, args, up, subs, path, binds, pos, raw, seen))
    case Shake.Many{}:
      gw.opt(val, name, args, up, subs, path, binds, pos, raw, seen)
    case Shake.Pos{}:
      ([], {==})
    case Shake.Rest{}:
      ([], {==})

# a found argument, or an unknown flag
law gw.arg:
  for found: Maybe<&2, Shake.Arg>
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), View{args, up,
      path, binds})

def gw.arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen):
  match found:
    case None{}:
      ([], {==})
    case Some{aa}:
      match aa:
        case Shake.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          gw.kind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option with a name, or `--=...`
law gw.named:
  for empty: Bool
  for +name: String
  for +val: Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw,
    seen), View{args, up, path, binds})

def gw.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw, seen):
  match empty:
    case True{}:
      ([], {==})
    case False{}:
      gw.arg(Shake.by_long(args, name), val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option after the `=` cut
law gw.cut:
  for nv: String & Maybe<&2, String>
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen):
  match nv:
    case (+name, val):
      gw.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option
law gw.long:
  for +body: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.long(body, orig, args, up, subs, path, binds, pos, raw, seen):
  gw.cut(Shake.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen)

# one letter of a cluster, read
law gw.apply:
  for st: Shake.St
  for +cc: Char
  for +rest: String
  for +orig: String
  gw.Stay(Shake.cluster.apply(st, cc, rest, orig), view(st))

def gw.apply(st, cc, rest, orig):
  match st:
    case Shake.St{_m, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gw.arg(Shake.by_short(args, SCon{cc, SNil{}}), Shake.cluster.val(Shake.by_short(args, SCon{cc, SNil{}}), rest),
        orig, args, up, subs, path, binds, pos, raw, seen)

# one letter of a cluster, unless an earlier one ended it
law gw.letter:
  for done: Bool
  for +cc: Char
  for +rest: String
  for +orig: String
  for +st: Shake.St
  gw.Stay(Shake.cluster.letter(done, cc, rest, orig, st), view(st))

def gw.letter(done, cc, rest, orig, st):
  match done:
    case True{}:
      gw.same_st(st)
    case False{}:
      gw.apply(st, cc, rest, orig)

# every letter of a cluster
law gw.cluster:
  for body: String
  for +orig: String
  for +st: Shake.St
  for +done: Bool
  gw.Stay(Shake.cluster(body, orig, st, done), view(st))

def gw.cluster(body, orig, st, done):
  match body:
    case SNil{}:
      gw.same_st(st)
    case SCon{+cc, +rest}:
      +next = Shake.cluster.letter(done, cc, rest, orig, st)
      gw.stay_chain(view(st), next, Shake.cluster(rest, orig, next, Shake.cluster.done(done, cc, rest, st)),
        gw.letter(done, cc, rest, orig, st),
        gw.cluster(rest, orig, next, Shake.cluster.done(done, cc, rest, st)))

# a short option word
law gw.short:
  for +body: String
  for +orig: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.take_short(body, orig, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.short(body, orig, args, up, subs, path, binds, pos, raw, seen):
  gw.cluster(body, orig, Shake.St{Shake.Free{}, args, up, subs, path, binds, pos, raw, seen}, False{})

# a plain word bound to the next positional, or refused
law gw.pos:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for pos: List<&2, Shake.Arg>
  for +raw: Bool
  gw.Stay(Shake.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), View{args, up, path, binds})

def gw.pos(tok, args, up, subs, path, binds, pos, raw):
  match pos:
    case Nil{}:
      ([], {==})
    case Con{hh, tt}:
      match hh:
        case Shake.Arg{+name, +sh, +lo, +kind, +hp, +req, +dflt, +cs}:
          gw.choice(Shake.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            Shake.parse.take_pos.keep(Shake.rest.is(Shake.Arg{name, sh, lo, kind, hp, req, dflt, cs}),
              Shake.Arg{name, sh, lo, kind, hp, req, dflt, cs}, tt), raw, True{})

# a view after entering subcommand `name`, whose arguments are `next`: the
# current command goes above, with its arguments and bindings
def gw.entered(+name: String, next: List<&2, Shake.Arg>, vv: View) -> View:
  View{args, up, path, binds} = vv
  View{next, Shake.Level{args, binds} <> up, List.append(&2, String, path, [name]), []}

# a walker that entered a subcommand from the command of `small`
def gw.Enter(big: Shake.St, small: View) -> Type:
  &name: String -> &next: List<&2, Shake.Arg> -> {view(big) == gw.entered(name, next, small) : View}

# whether a mode can still finish as a success
def gw.live.mode(mode: Shake.Mode) -> Bool:
  match mode:
    case Shake.Free{}:
      True{}
    case Shake.Need{_n}:
      True{}
    case Shake.Help{}:
      False{}
    case Shake.Dead{_e}:
      False{}

# whether a walker can still finish as a success: free, or waiting for a
# value; one reading a help path or failed never can
def gw.live(st: Shake.St) -> Bool:
  Shake.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  gw.live.mode(mode)

# a walker that can no longer finish as a success
def gw.Stuck(big: Shake.St) -> Type:
  {gw.live(big) == False{} : Bool}

# the three things a word does to a walker
type Moved<-A: Type, -B: Type, -C: Type> is Type:
  Stays{proof: A}
  Enters{proof: B}
  Stops{proof: C}

# what one word did to a walker whose view was `small`
def gw.Step(big: Shake.St, small: View) -> Type:
  Moved<gw.Stay(big, small), gw.Enter(big, small), gw.Stuck(big)>

# entering a subcommand
law gw.enter:
  for ss: Shake.Sub
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  gw.Enter(Shake.parse.enter(ss, args, up, path, binds), View{args, up, path, binds})

def gw.enter(ss, _args, _up, _path, _binds):
  match ss:
    case Shake.Sub{+name, _a, +next, _c}:
      (name, (next, {==}))

# a subcommand entered, or a required positional missing
law gw.enter_or:
  for miss: Maybe<&2, String>
  for ss: Shake.Sub
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Step(Shake.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.enter_or(miss, ss, args, up, _subs, path, binds, _pos, _raw, _seen):
  match miss:
    case None{}:
      Enters{gw.enter(ss, args, up, path, binds)}
    case Some{_n}:
      Stays{([], {==})}

# a found subcommand, or a positional
law gw.word_go:
  for found: Maybe<&2, Shake.Sub>
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Step(Shake.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.word_go(found, tok, args, up, subs, path, binds, pos, raw, seen):
  match found:
    case None{}:
      Stays{gw.pos(tok, args, up, subs, path, binds, pos, raw)}
    case Some{ss}:
      gw.enter_or(Shake.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen)

# a plain word
law gw.word:
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Step(Shake.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), View{args, up, path, binds})

def gw.word(tok, args, up, subs, path, binds, pos, raw, seen):
  gw.word_go(Shake.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen)

# `-` as a word, or a short option
law gw.short_go:
  for alone: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), View{args, up, path, binds})

def gw.short_go(alone, tok, args, up, subs, path, binds, pos, seen):
  match alone:
    case True{}:
      gw.word(tok, args, up, subs, path, binds, pos, False{}, seen)
    case False{}:
      Stays{gw.short(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, False{}, seen)}

# a word that starts with `-`, or not
law gw.step_short:
  for dash: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), View{args, up, path, binds})

def gw.step_short(dash, tok, args, up, subs, path, binds, pos, seen):
  match dash:
    case True{}:
      gw.short_go(String.eq(tok, "-"), tok, args, up, subs, path, binds, pos, seen)
    case False{}:
      gw.word(tok, args, up, subs, path, binds, pos, False{}, seen)

# a long option, a short option, or a word
law gw.kind_go:
  for long: Bool
  for +dash: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen),
    View{args, up, path, binds})

def gw.kind_go(long, dash, tok, args, up, subs, path, binds, pos, seen):
  match long:
    case True{}:
      Stays{gw.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen)}
    case False{}:
      gw.step_short(dash, tok, args, up, subs, path, binds, pos, seen)

# `help`, or any other word
law gw.help:
  for hit: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), View{args, up, path, binds})

def gw.help(hit, tok, args, up, subs, path, binds, pos, seen):
  match hit:
    case True{}:
      Stays{([], {==})}
    case False{}:
      gw.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds,
        pos, seen)

# `--`, or any other word
law gw.end:
  for end: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), View{args, up, path, binds})

def gw.end(end, tok, args, up, subs, path, binds, pos, seen):
  match end:
    case True{}:
      Stays{([], {==})}
    case False{}:
      gw.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen)

# a free walker, before or after `--`
law gw.raw:
  for raw: Bool
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +seen: Bool
  gw.Step(Shake.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), View{args, up, path, binds})

def gw.raw(raw, tok, args, up, subs, path, binds, pos, seen):
  match raw:
    case True{}:
      Stays{gw.pos(tok, args, up, subs, path, binds, pos, True{})}
    case False{}:
      gw.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen)

# an option's value, or a flag-shaped word where it was wanted
law gw.need:
  for flag: Bool
  for +name: String
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stay(Shake.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen),
    View{args, up, path, binds})

def gw.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen):
  match flag:
    case True{}:
      ([], {==})
    case False{}:
      gw.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen)

# a word after `help` leaves the walker reading a help path, or failed
law gw.help_path:
  for found: Maybe<&2, Shake.Sub>
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Stuck(Shake.parse.step.help_path(found, tok, args, up, subs, path, binds, pos, raw, seen))

def gw.help_path(found, _tok, _args, _up, _subs, _path, _binds, _pos, _raw, _seen):
  match found:
    case None{}:
      {==}
    case Some{ss}:
      match ss:
        case Shake.Sub{_n, _a, _g, _c}:
          {==}

# one word, in each mode
law gw.mode:
  for mode: Shake.Mode
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  gw.Step(Shake.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen),
    View{args, up, path, binds})

def gw.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen):
  match mode:
    case Shake.Dead{_e}:
      Stops{{==}}
    case Shake.Need{name}:
      Stays{gw.need(Shake.looks_flag(tok), name, tok, args, up, subs, path, binds, pos, raw, seen)}
    case Shake.Help{}:
      Stops{gw.help_path(Shake.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen)}
    case Shake.Free{}:
      gw.raw(raw, tok, args, up, subs, path, binds, pos, seen)

# LAW: one word stays in the current command, putting bindings in front of
# its own (one per letter of a cluster), or enters a subcommand, or leaves the
# walker stuck
law gw.step:
  for +tok: String
  for st: Shake.St
  gw.Step(Shake.parse.step(tok, st), view(st))

def gw.step(tok, st):
  match st:
    case Shake.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gw.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen)

# a path with nothing after it
law gw.nil_s:
  for pp: List<&2, String>
  {List.append(&2, String, pp, []) == pp : List<&2, String>}

def gw.nil_s(pp):
  match pp:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => hh <> xs, List.append(&2, String, tt, []), tt,
        gw.nil_s(tt))

# appending names is associative
law gw.sapp:
  for +aa: List<&2, String>
  for +bb: List<&2, String>
  for +cc: List<&2, String>
  {List.append(&2, String, List.append(&2, String, aa, bb), cc)
    == List.append(&2, String, aa, List.append(&2, String, bb, cc)) : List<&2, String>}

def gw.sapp(aa, bb, cc):
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => hh <> xs,
        List.append(&2, String, List.append(&2, String, tt, bb), cc),
        List.append(&2, String, tt, List.append(&2, String, bb, cc)), gw.sapp(tt, bb, cc))

# appending levels is associative
law gw.lapp:
  for +aa: List<&2, Shake.Level>
  for +bb: List<&2, Shake.Level>
  for +cc: List<&2, Shake.Level>
  {List.append(&2, Shake.Level, List.append(&2, Shake.Level, aa, bb), cc)
    == List.append(&2, Shake.Level, aa, List.append(&2, Shake.Level, bb, cc)) : List<&2, Shake.Level>}

def gw.lapp(aa, bb, cc):
  match aa:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.cong(List<&2, Shake.Level>, List<&2, Shake.Level>, xs => hh <> xs,
        List.append(&2, Shake.Level, List.append(&2, Shake.Level, tt, bb), cc),
        List.append(&2, Shake.Level, tt, List.append(&2, Shake.Level, bb, cc)), gw.lapp(tt, bb, cc))

# one level after a list makes it one longer
law gw.len_snoc:
  for qs: List<&2, Shake.Level>
  for +ll: Shake.Level
  {List.length(&2, Shake.Level, List.append(&2, Shake.Level, qs, [ll])) == 1n+List.length(&2, Shake.Level, qs)
    : Nat}

def gw.len_snoc(qs, ll):
  match qs:
    case Nil{}:
      {==}
    case Con{_h, tt}:
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Shake.Level, List.append(&2, Shake.Level, tt, [ll])),
        1n+List.length(&2, Shake.Level, tt), gw.len_snoc(tt, ll))

# the levels of a walker, its current command first, and its selected path
type Frame is Data:
  Frame{levels: List<&2, Shake.Level>, path: List<&2, String>}

# a walker's frame
def gw.frame(st: Shake.St) -> Frame:
  Shake.St{_m, args, up, _s, path, binds, _o, _r, _n} = st
  Frame{Shake.Level{args, binds} <> up, path}

# the frame of a walker grown from `vv`: new levels `qs` in front of its own,
# whose bindings have `xs` in front, and names `ms` after its path
def gw.grown(
  +xs: List<&2, Shake.Bind>,
  +qs: List<&2, Shake.Level>,
  +ms: List<&2, String>,
  vv: View
) -> Frame:
  View{args, up, path, binds} = vv
  Frame{List.append(&2, Shake.Level, qs, Shake.Level{args, List.append(&2, Shake.Bind, xs, binds)} <> up),
    List.append(&2, String, path, ms)}

# a walker grown from the view `small`: its command, with bindings in front,
# sits under as many new levels as new names follow the path
def gw.Grown(big: Shake.St, small: View) -> Type:
  &xs: List<&2, Shake.Bind> -> &qs: List<&2, Shake.Level> -> &ms: List<&2, String>
    -> &_h: {List.length(&2, Shake.Level, qs) == List.length(&2, String, ms) : Nat}
    -> {gw.frame(big) == gw.grown(xs, qs, ms, small) : Frame}

# a walker is grown from itself
law gw.grown_refl:
  for st: Shake.St
  gw.Grown(st, view(st))

def gw.grown_refl(st):
  match st:
    case Shake.St{_m, +args, +up, _s, +path, +binds, _o, _r, _n}:
      ([], ([], ([], ({==},
        Equal.cong(List<&2, String>, Frame, pp => Frame{Shake.Level{args, binds} <> up, pp}, path,
          List.append(&2, String, path, []), Equal.sym(List<&2, String>, List.append(&2, String, path, []), path,
            gw.nil_s(path)))))))

# bindings put in front, then grown
law gw.grown_put:
  for +xs: List<&2, Shake.Bind>
  for +ys: List<&2, Shake.Bind>
  for +qs: List<&2, Shake.Level>
  for +ms: List<&2, String>
  for vv: View
  {gw.grown(xs, qs, ms, gw.put(ys, vv)) == gw.grown(List.append(&2, Shake.Bind, xs, ys), qs, ms, vv) : Frame}

def gw.grown_put(xs, ys, qs, ms, vv):
  match vv:
    case View{+args, +up, +path, +binds}:
      Equal.cong(List<&2, Shake.Bind>, Frame,
        bs => Frame{List.append(&2, Shake.Level, qs, Shake.Level{args, bs} <> up), List.append(&2, String, path, ms)},
        List.append(&2, Shake.Bind, xs, List.append(&2, Shake.Bind, ys, binds)),
        List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, xs, ys), binds),
        Equal.sym(List<&2, Shake.Bind>, List.append(&2, Shake.Bind, List.append(&2, Shake.Bind, xs, ys), binds),
          List.append(&2, Shake.Bind, xs, List.append(&2, Shake.Bind, ys, binds)), gw.app(xs, ys, binds)))

# a subcommand entered, then grown
law gw.grown_enter:
  for +xs: List<&2, Shake.Bind>
  for +qs: List<&2, Shake.Level>
  for +ms: List<&2, String>
  for +name: String
  for +next: List<&2, Shake.Arg>
  for vv: View
  {gw.grown(xs, qs, ms, gw.entered(name, next, vv))
    == gw.grown([], List.append(&2, Shake.Level, qs, [Shake.Level{next, List.append(&2, Shake.Bind, xs, [])}]),
      name <> ms, vv) : Frame}

def gw.grown_enter(xs, qs, ms, name, next, vv):
  match vv:
    case View{+args, +up, +path, +binds}:
      +lq = {Shake.Level{next, List.append(&2, Shake.Bind, xs, [])} : Shake.Level}
      +ll = {Shake.Level{args, binds} <> up : List<&2, Shake.Level>}
      Equal.trans(Frame,
        Frame{List.append(&2, Shake.Level, qs, lq <> ll), List.append(&2, String, List.append(&2, String, path, [name]),
          ms)},
        Frame{List.append(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq]), ll),
          List.append(&2, String, List.append(&2, String, path, [name]), ms)},
        Frame{List.append(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq]), ll),
          List.append(&2, String, path, name <> ms)},
        Equal.cong(List<&2, Shake.Level>, Frame,
          ls => Frame{ls, List.append(&2, String, List.append(&2, String, path, [name]), ms)},
          List.append(&2, Shake.Level, qs, lq <> ll), List.append(&2, Shake.Level, List.append(&2, Shake.Level,
              qs, [lq]), ll),
          Equal.sym(List<&2, Shake.Level>, List.append(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq]), ll),
            List.append(&2, Shake.Level, qs, lq <> ll), gw.lapp(qs, [lq], ll))),
        Equal.cong(List<&2, String>, Frame,
          ps => Frame{List.append(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq]), ll), ps},
          List.append(&2, String, List.append(&2, String, path, [name]), ms), List.append(&2, String, path, name <> ms),
          gw.sapp(path, [name], ms)))

# staying, then growing, is growing
law gw.after_stay:
  for +v0: View
  for +st1: Shake.St
  for +st2: Shake.St
  for ss: gw.Stay(st1, v0)
  for gg: gw.Grown(st2, view(st1))
  gw.Grown(st2, v0)

def gw.after_stay(v0, st1, st2, ss, gg):
  (x1, e1) = ss
  (x2, r2) = gg
  (q2, r3) = r2
  (m2, r4) = r3
  (hl, e2) = r4
  +ys = {x1 : List<&2, Shake.Bind>}
  +xs = {x2 : List<&2, Shake.Bind>}
  +qs = {q2 : List<&2, Shake.Level>}
  +ms = {m2 : List<&2, String>}
  (List.append(&2, Shake.Bind, xs, ys), (qs, (ms, (hl,
    Equal.trans(Frame, gw.frame(st2), gw.grown(xs, qs, ms, view(st1)),
      gw.grown(List.append(&2, Shake.Bind, xs, ys), qs, ms, v0), e2,
      Equal.trans(Frame, gw.grown(xs, qs, ms, view(st1)), gw.grown(xs, qs, ms, gw.put(ys, v0)),
        gw.grown(List.append(&2, Shake.Bind, xs, ys), qs, ms, v0),
        Equal.cong(View, Frame, vv => gw.grown(xs, qs, ms, vv), view(st1), gw.put(ys, v0), e1),
        gw.grown_put(xs, ys, qs, ms, v0)))))))

# entering, then growing, is growing
law gw.after_enter:
  for +v0: View
  for +st1: Shake.St
  for +st2: Shake.St
  for ee: gw.Enter(st1, v0)
  for gg: gw.Grown(st2, view(st1))
  gw.Grown(st2, v0)

def gw.after_enter(v0, st1, st2, ee, gg):
  (n1, r1) = ee
  (t1, e1) = r1
  (x2, r2) = gg
  (q2, r3) = r2
  (m2, r4) = r3
  (hl, e2) = r4
  +name = {n1 : String}
  +next = {t1 : List<&2, Shake.Arg>}
  +xs = {x2 : List<&2, Shake.Bind>}
  +qs = {q2 : List<&2, Shake.Level>}
  +ms = {m2 : List<&2, String>}
  +lq = {Shake.Level{next, List.append(&2, Shake.Bind, xs, [])} : Shake.Level}
  ([], (List.append(&2, Shake.Level, qs, [lq]), (name <> ms,
    (Equal.trans(Nat, List.length(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq])),
      1n+List.length(&2, Shake.Level, qs), 1n+List.length(&2, String, ms), gw.len_snoc(qs, lq),
      Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Shake.Level, qs), List.length(&2, String, ms), hl)),
    Equal.trans(Frame, gw.frame(st2), gw.grown(xs, qs, ms, view(st1)),
      gw.grown([], List.append(&2, Shake.Level, qs, [lq]), name <> ms, v0), e2,
      Equal.trans(Frame, gw.grown(xs, qs, ms, view(st1)), gw.grown(xs, qs, ms, gw.entered(name, next, v0)),
        gw.grown([], List.append(&2, Shake.Level, qs, [lq]), name <> ms, v0),
        Equal.cong(View, Frame, vv => gw.grown(xs, qs, ms, vv), view(st1), gw.entered(name, next, v0), e1),
        gw.grown_enter(xs, qs, ms, name, next, v0)))))))

# True is never False
law gw.true_false:
  for ee: {True{} == False{} : Bool}
  Empty

# Unit for True, Empty for False: a motive that tells them apart
def gw.true_ty(bb: Bool) -> Type:
  match bb:
    case True{}:
      Unit
    case False{}:
      Empty

def gw.true_false(ee):
  %ee : gw.true_ty(_)
  Unit{}

# what `gw.stuck_mode` claims of a mode
def gw.stuck_mode.ty(
  mode: Shake.Mode,
  +tok: String,
  +args: List<&2, Shake.Arg>,
  +up: List<&2, Shake.Level>,
  +subs: List<&2, Shake.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, Shake.Bind>,
  +pos: List<&2, Shake.Arg>,
  +raw: Bool,
  +seen: Bool
) -> Type:
  gw.Stuck(Shake.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen))

# a mode that cannot finish as a success stays so
law gw.stuck_mode:
  for mode: Shake.Mode
  for +tok: String
  for +args: List<&2, Shake.Arg>
  for +up: List<&2, Shake.Level>
  for +subs: List<&2, Shake.Sub>
  for +path: List<&2, String>
  for +binds: List<&2, Shake.Bind>
  for +pos: List<&2, Shake.Arg>
  for +raw: Bool
  for +seen: Bool
  for hh: {gw.live.mode(mode) == False{} : Bool}
  gw.stuck_mode.ty(mode, tok, args, up, subs, path, binds, pos, raw, seen)

def gw.stuck_mode(mode, tok, args, up, subs, path, binds, pos, raw, seen, hh):
  match mode:
    case Shake.Free{}:
      Empty.absurd(gw.stuck_mode.ty(Shake.Free{}, tok, args, up, subs, path, binds, pos, raw, seen),
        gw.true_false(hh))
    case Shake.Need{+nn}:
      Empty.absurd(gw.stuck_mode.ty(Shake.Need{nn}, tok, args, up, subs, path, binds, pos, raw, seen),
        gw.true_false(hh))
    case Shake.Help{}:
      gw.help_path(Shake.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen)
    case Shake.Dead{_e}:
      {==}

# a stuck walker stays stuck on the next word
law gw.stuck_step:
  for +tok: String
  for st: Shake.St
  for hh: gw.Stuck(st)
  gw.Stuck(Shake.parse.step(tok, st))

def gw.stuck_step(tok, st, hh):
  match st:
    case Shake.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gw.stuck_mode(mode, tok, args, up, subs, path, binds, pos, raw, seen, hh)

# a stuck walker stays stuck, whatever words follow
law gw.stuck_walk:
  for more: List<&2, String>
  for +st: Shake.St
  for hh: gw.Stuck(st)
  gw.Stuck(Shake.parse.walk(more, st))

def gw.stuck_walk(more, st, hh):
  match more:
    case Nil{}:
      hh
    case Con{+ww, +tt}:
      gw.stuck_walk(tt, Shake.parse.step(ww, st), gw.stuck_step(ww, st, hh))

# a walk either grows the walker or leaves it stuck
type Went<-A: Type, -B: Type> is Type:
  Grew{proof: A}
  Stopped{proof: B}

# what a walk did to a walker whose view was `small`
def gw.Reach(big: Shake.St, small: View) -> Type:
  Went<gw.Grown(big, small), gw.Stuck(big)>

# one word, then a walk
law gw.reach.cons:
  for +tt: List<&2, String>
  for +st0: Shake.St
  for +st1: Shake.St
  for ss: gw.Step(st1, view(st0))
  for rr: gw.Reach(Shake.parse.walk(tt, st1), view(st1))
  gw.Reach(Shake.parse.walk(tt, st1), view(st0))

def gw.reach.cons(tt, st0, st1, ss, rr):
  match ss:
    case Stays{ww}:
      match rr:
        case Grew{gg}:
          Grew{gw.after_stay(view(st0), st1, Shake.parse.walk(tt, st1), ww, gg)}
        case Stopped{hh}:
          Stopped{hh}
    case Enters{ww}:
      match rr:
        case Grew{gg}:
          Grew{gw.after_enter(view(st0), st1, Shake.parse.walk(tt, st1), ww, gg)}
        case Stopped{hh}:
          Stopped{hh}
    case Stops{hh}:
      Stopped{gw.stuck_walk(tt, st1, hh)}

# LAW: whatever words it reads, a walker either keeps its current command's
# arguments and bindings, with bindings in front, under any subcommands it
# enters, one per name its path gains, or can no longer finish as a success
law gw.reach:
  for more: List<&2, String>
  for +st: Shake.St
  gw.Reach(Shake.parse.walk(more, st), view(st))

def gw.reach(more, st):
  match more:
    case Nil{}:
      Grew{gw.grown_refl(st)}
    case Con{+ww, +tt}:
      gw.reach.cons(tt, st, Shake.parse.step(ww, st), gw.step(ww, st), gw.reach(tt, Shake.parse.step(ww, st)))

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
      gw.esame(rest)
    case False{}:
      gw.eone(Shake.Bind{name, val}, rest)

# an argument with a default, or none
law gw.fill_go:
  for dd: Maybe<&2, String>
  for +name: String
  for +binds: List<&2, Shake.Bind>
  gw.Ext(Shake.fill.arg.go(dd, name, binds), binds)

def gw.fill_go(dd, name, binds):
  match dd:
    case None{}:
      gw.esame(binds)
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
      gw.esame(binds)
    case Con{+hh, +tt}:
      gw.chain(binds, Shake.fill.args(tt, binds), Shake.fill.arg(hh, Shake.fill.args(tt, binds)),
        gw.fill(tt, binds), gw.fill_arg(hh, Shake.fill.args(tt, binds)))

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

# the Matched of a success, or an empty one for a failure
def gw.done_of(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> Shake.Matched:
  match rr:
    case Done{mm}:
      mm
    case Fail{_e}:
      Shake.Leaf{[]}

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

# the Matched a finished frame builds: each command's defaults filled, root
# first, under the path
def gw.build_of(fr: Frame) -> Shake.Matched:
  Frame{lvs, path} = fr
  Shake.matched.build(List.reverse(&2, Shake.Level, Shake.fill.levels(lvs)), path)

# a success after the required check is the Matched built from the levels
law gw.miss_done:
  for mm: Maybe<&2, String>
  for +path: List<&2, String>
  for +lvs: List<&2, Shake.Level>
  for +found: Shake.Matched
  for hh: {Shake.parse.finish.miss(mm, path, lvs) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {found == Shake.matched.build(lvs, path) : Shake.Matched}

def gw.miss_done(mm, path, lvs, found, hh):
  match mm:
    case Some{nn}:
      Empty.absurd({found == Shake.matched.build(lvs, path) : Shake.Matched},
        gw.fail_done(Shake.Missing{path, nn}, found, hh))
    case None{}:
      Equal.sym(Shake.Matched, Shake.matched.build(lvs, path), found,
        Equal.cong(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Shake.Matched, rr => gw.done_of(rr),
          Done{Shake.matched.build(lvs, path)}, Done{found}, hh))

# LAW: a walker that finishes as a success gives the Matched its frame builds
law gw.finished:
  for fs: Shake.St
  for +found: Shake.Matched
  for hh: {Shake.parse.finish(fs) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {found == gw.build_of(gw.frame(fs)) : Shake.Matched}

def gw.finished(fs, found, hh):
  match fs:
    case Shake.St{Shake.Free{}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      +lvs = List.reverse(&2, Shake.Level, Shake.fill.levels(Shake.Level{args, binds} <> up))
      gw.miss_done(Shake.miss.levels(lvs), path, lvs, found, hh)
    case Shake.St{Shake.Dead{+ee}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd({found == gw.build_of(Frame{Shake.Level{args, binds} <> up, path}) : Shake.Matched},
        gw.fail_done(ee, found, hh))
    case Shake.St{Shake.Need{+nn}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd({found == gw.build_of(Frame{Shake.Level{args, binds} <> up, path}) : Shake.Matched},
        gw.fail_done(Shake.NoValue{path, nn}, found, hh))
    case Shake.St{Shake.Help{}, +args, +up, _s, +path, +binds, _o, _r, _n}:
      Empty.absurd({found == gw.build_of(Frame{Shake.Level{args, binds} <> up, path}) : Shake.Matched},
        gw.fail_done(Shake.NeedHelp{path}, found, hh))

# a stuck walker never finishes as a success
law gw.live_done:
  for fs: Shake.St
  for +found: Shake.Matched
  for hh: {Shake.parse.finish(fs) == Done{found} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: gw.Stuck(fs)
  Empty

def gw.live_done(fs, found, hh, hs):
  match fs:
    case Shake.St{Shake.Free{}, _a, _g, _s, _p, _b, _o, _r, _n}:
      gw.true_false(hs)
    case Shake.St{Shake.Need{_nn}, _a, _g, _s, _p, _b, _o, _r, _n}:
      gw.true_false(hs)
    case Shake.St{Shake.Dead{+ee}, _a, _g, _s, _p, _b, _o, _r, _n}:
      gw.fail_done(ee, found, hh)
    case Shake.St{Shake.Help{}, _a, _g, _s, +path, _b, _o, _r, _n}:
      gw.fail_done(Shake.NeedHelp{path}, found, hh)

# filling defaults level by level, around one level
law gw.fill_mid:
  for qs: List<&2, Shake.Level>
  for +args: List<&2, Shake.Arg>
  for +binds: List<&2, Shake.Bind>
  for +up: List<&2, Shake.Level>
  {Shake.fill.levels(List.append(&2, Shake.Level, qs, Shake.Level{args, binds} <> up))
    == List.append(&2, Shake.Level, Shake.fill.levels(qs),
      Shake.Level{args, Shake.fill.args(args, binds)} <> Shake.fill.levels(up)) : List<&2, Shake.Level>}

def gw.fill_mid(qs, args, binds, up):
  match qs:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      match hh:
        case Shake.Level{+aa, +bb}:
          Equal.cong(List<&2, Shake.Level>, List<&2, Shake.Level>, xs => Shake.Level{aa, Shake.fill.args(aa, bb)} <> xs,
            Shake.fill.levels(List.append(&2, Shake.Level, tt, Shake.Level{args, binds} <> up)),
            List.append(&2, Shake.Level, Shake.fill.levels(tt),
              Shake.Level{args, Shake.fill.args(args, binds)} <> Shake.fill.levels(up)),
            gw.fill_mid(tt, args, binds, up))

# reversing levels onto a list is reversing, then appending it
law gw.lrev_go:
  for xs: List<&2, Shake.Level>
  for +acc: List<&2, Shake.Level>
  {List.reverse.go(&2, Shake.Level, xs, acc)
    == List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, xs, []), acc) : List<&2, Shake.Level>}

def gw.lrev_go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, Shake.Level>, List.reverse.go(&2, Shake.Level, tt, hh <> acc),
        List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, []), hh <> acc),
        List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, [hh]), acc),
        gw.lrev_go(tt, hh <> acc),
        Equal.sym(List<&2, Shake.Level>, List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, [hh]), acc),
          List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, []), hh <> acc),
          Equal.trans(List<&2, Shake.Level>,
            List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, [hh]), acc),
            List.append(&2, Shake.Level, List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, []), [hh]),
              acc),
            List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, []), hh <> acc),
            Equal.cong(List<&2, Shake.Level>, List<&2, Shake.Level>, ys => List.append(&2, Shake.Level, ys, acc),
              List.reverse.go(&2, Shake.Level, tt, [hh]),
              List.append(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, []), [hh]), gw.lrev_go(tt, [hh])),
            gw.lapp(List.reverse.go(&2, Shake.Level, tt, []), [hh], acc))))

# reversing two lists of levels one after the other onto a list
law gw.lrev_app:
  for xs: List<&2, Shake.Level>
  for +ys: List<&2, Shake.Level>
  for +acc: List<&2, Shake.Level>
  {List.reverse.go(&2, Shake.Level, List.append(&2, Shake.Level, xs, ys), acc)
    == List.reverse.go(&2, Shake.Level, ys, List.reverse.go(&2, Shake.Level, xs, acc)) : List<&2, Shake.Level>}

def gw.lrev_app(xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      gw.lrev_app(tt, ys, hh <> acc)

# the levels around one, reversed: those after it reversed, it, then those
# before it reversed
law gw.lrev_mid:
  for +fq: List<&2, Shake.Level>
  for +f0: Shake.Level
  for +fu: List<&2, Shake.Level>
  {List.reverse(&2, Shake.Level, List.append(&2, Shake.Level, fq, f0 <> fu))
    == List.append(&2, Shake.Level, List.reverse(&2, Shake.Level, fu), f0 <> List.reverse(&2, Shake.Level, fq))
    : List<&2, Shake.Level>}

def gw.lrev_mid(fq, f0, fu):
  Equal.trans(List<&2, Shake.Level>, List.reverse(&2, Shake.Level, List.append(&2, Shake.Level, fq, f0 <> fu)),
    List.reverse.go(&2, Shake.Level, fu, f0 <> List.reverse(&2, Shake.Level, fq)),
    List.append(&2, Shake.Level, List.reverse(&2, Shake.Level, fu), f0 <> List.reverse(&2, Shake.Level, fq)),
    gw.lrev_app(fq, f0 <> fu, []), gw.lrev_go(fu, f0 <> List.reverse(&2, Shake.Level, fq)))

# Unit for zero, Empty for a successor: a motive that tells them apart
def gw.zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# zero is never a successor
law gw.zero_succ:
  for +nn: Nat
  for ee: {0n == 1n+nn : Nat}
  Empty

def gw.zero_succ(_nn, ee):
  %ee : gw.zero_ty(_)
  Unit{}

# a successor is never zero
law gw.succ_zero:
  for +nn: Nat
  for ee: {1n+nn == 0n : Nat}
  Empty

def gw.succ_zero(nn, ee):
  gw.zero_succ(nn, Equal.sym(Nat, 1n+nn, 0n, ee))

# the number before a successor
def gw.pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# what `gw.at_build` claims
def gw.at_build.ty(
  +r0: List<&2, Shake.Level>,
  +p0: List<&2, String>,
  +f0: Shake.Level,
  +rq: List<&2, Shake.Level>,
  +ms: List<&2, String>
) -> Type:
  {Shake.at(Shake.matched.build(List.append(&2, Shake.Level, r0, f0 <> rq), List.append(&2, String, p0, ms)), p0)
    == Some{Shake.matched.build(f0 <> rq, ms)} : Maybe<&2, Shake.Matched>}

# LAW: following a path as long as the levels above one reaches that level's
# Matched
law gw.at_build:
  for r0: List<&2, Shake.Level>
  for p0: List<&2, String>
  for +f0: Shake.Level
  for +rq: List<&2, Shake.Level>
  for +ms: List<&2, String>
  for hl: {List.length(&2, Shake.Level, r0) == List.length(&2, String, p0) : Nat}
  gw.at_build.ty(r0, p0, f0, rq, ms)

def gw.at_build(r0, p0, f0, rq, ms, hl):
  match r0:
    case Nil{}:
      match p0:
        case Nil{}:
          {==}
        case Con{+ph, +pt}:
          Empty.absurd(gw.at_build.ty([], ph <> pt, f0, rq, ms), gw.zero_succ(List.length(&2, String, pt), hl))
    case Con{+ll, +rt}:
      match p0:
        case Nil{}:
          Empty.absurd(gw.at_build.ty(ll <> rt, [], f0, rq, ms), gw.succ_zero(List.length(&2, Shake.Level, rt), hl))
        case Con{+ph, +pt}:
          ee = Equal.sym(Bool, String.eq(ph, ph), True{}, Eq.string_eq_self(ph))
          %ee : {Shake.at.go(pt, Shake.sub_of.pick(_,
              Shake.matched.build(List.append(&2, Shake.Level, rt, f0 <> rq), List.append(&2, String, pt, ms))))
            == Some{Shake.matched.build(f0 <> rq, ms)} : Maybe<&2, Shake.Matched>}
          gw.at_build(rt, pt, f0, rq, ms,
            Equal.cong(Nat, Nat, nn => gw.pred(nn), 1n+List.length(&2, Shake.Level, rt), 1n+List.length(&2, String, pt),
              hl))

# LAW: a command's Matched reads its own level's bindings, reversed, whether
# a subcommand was selected under it or not
law gw.own_build:
  for +f0: Shake.Level
  for +rq: List<&2, Shake.Level>
  for ms: List<&2, String>
  {Shake.own(Shake.matched.build(f0 <> rq, ms)) == List.reverse(&2, Shake.Bind, Shake.level.binds(f0))
    : List<&2, Shake.Bind>}

def gw.own_build(_f0, _rq, ms):
  match ms:
    case Nil{}:
      {==}
    case Con{_m, _t}:
      {==}

# filling defaults keeps the number of levels
law gw.len_fill:
  for up: List<&2, Shake.Level>
  {List.length(&2, Shake.Level, Shake.fill.levels(up)) == List.length(&2, Shake.Level, up) : Nat}

def gw.len_fill(up):
  match up:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      match hh:
        case Shake.Level{_a, _b}:
          Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Shake.Level, Shake.fill.levels(tt)),
            List.length(&2, Shake.Level, tt), gw.len_fill(tt))

# adding a successor
law gw.add_succ:
  for aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

def gw.add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), gw.add_succ(pp, bb))

# adding zero
law gw.add_zero:
  for aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

def gw.add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(pp, 0n), pp, gw.add_zero(pp))

# reversing onto a list adds the lengths
law gw.len_rev_go:
  for xs: List<&2, Shake.Level>
  for +acc: List<&2, Shake.Level>
  {List.length(&2, Shake.Level, List.reverse.go(&2, Shake.Level, xs, acc))
    == Nat.add(List.length(&2, Shake.Level, xs), List.length(&2, Shake.Level, acc)) : Nat}

def gw.len_rev_go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(Nat, List.length(&2, Shake.Level, List.reverse.go(&2, Shake.Level, tt, hh <> acc)),
        Nat.add(List.length(&2, Shake.Level, tt), 1n+List.length(&2, Shake.Level, acc)),
        1n+Nat.add(List.length(&2, Shake.Level, tt), List.length(&2, Shake.Level, acc)),
        gw.len_rev_go(tt, hh <> acc),
        gw.add_succ(List.length(&2, Shake.Level, tt), List.length(&2, Shake.Level, acc)))

# reversing keeps the length
law gw.len_rev:
  for +xs: List<&2, Shake.Level>
  {List.length(&2, Shake.Level, List.reverse(&2, Shake.Level, xs)) == List.length(&2, Shake.Level, xs) : Nat}

def gw.len_rev(xs):
  Equal.trans(Nat, List.length(&2, Shake.Level, List.reverse(&2, Shake.Level, xs)),
    Nat.add(List.length(&2, Shake.Level, xs), 0n), List.length(&2, Shake.Level, xs), gw.len_rev_go(xs, []),
    gw.add_zero(List.length(&2, Shake.Level, xs)))

# a frame's levels
def gw.flevels(fr: Frame) -> List<&2, Shake.Level>:
  Frame{lvs, _p} = fr
  lvs

# a frame's path
def gw.fpath(fr: Frame) -> List<&2, String>:
  Frame{_l, path} = fr
  path

# a walker with one level more than names on its path
def gw.Deep(st: Shake.St) -> Type:
  {List.length(&2, Shake.Level, gw.flevels(gw.frame(st))) == 1n+List.length(&2, String, gw.fpath(gw.frame(st))) : Nat}

# the depth, from the grown frame's two parts
def gw.depth.go(
  +st: Shake.St,
  +a0: List<&2, Shake.Arg>,
  +b0: List<&2, Shake.Bind>,
  +xs: List<&2, Shake.Bind>,
  +qs: List<&2, Shake.Level>,
  +ms: List<&2, String>,
  hl: {List.length(&2, Shake.Level, qs) == List.length(&2, String, ms) : Nat},
  +ee: {gw.frame(st) == gw.grown(xs, qs, ms, View{a0, [], [], b0}) : Frame}
) -> gw.Deep(st):
  +lq = {Shake.Level{a0, List.append(&2, Shake.Bind, xs, b0)} : Shake.Level}
  Equal.trans(Nat, List.length(&2, Shake.Level, gw.flevels(gw.frame(st))),
    List.length(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq])),
    1n+List.length(&2, String, gw.fpath(gw.frame(st))),
    Equal.cong(Frame, Nat, fr => List.length(&2, Shake.Level, gw.flevels(fr)), gw.frame(st),
      gw.grown(xs, qs, ms, View{a0, [], [], b0}), ee),
    Equal.trans(Nat, List.length(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq])),
      1n+List.length(&2, String, ms), 1n+List.length(&2, String, gw.fpath(gw.frame(st))),
      Equal.trans(Nat, List.length(&2, Shake.Level, List.append(&2, Shake.Level, qs, [lq])),
        1n+List.length(&2, Shake.Level, qs), 1n+List.length(&2, String, ms), gw.len_snoc(qs, lq),
        Equal.cong(Nat, Nat, nn => 1n+nn, List.length(&2, Shake.Level, qs), List.length(&2, String, ms), hl)),
      Equal.cong(Frame, Nat, fr => 1n+List.length(&2, String, gw.fpath(fr)),
        gw.grown(xs, qs, ms, View{a0, [], [], b0}), gw.frame(st),
        Equal.sym(Frame, gw.frame(st), gw.grown(xs, qs, ms, View{a0, [], [], b0}), ee))))

# LAW: a walker grown from a root has one level more than names on its path
law gw.depth:
  for st: Shake.St
  for +a0: List<&2, Shake.Arg>
  for +b0: List<&2, Shake.Bind>
  for gg: gw.Grown(st, View{a0, [], [], b0})
  gw.Deep(st)

def gw.depth(st, a0, b0, gg):
  (x1, r1) = gg
  (q1, r2) = r1
  (m1, r3) = r2
  (hl, ee) = r3
  gw.depth.go(st, a0, b0, x1, q1, m1, hl, ee)

# a view's frame
def gw.vframe(vv: View) -> Frame:
  View{args, up, path, binds} = vv
  Frame{Shake.Level{args, binds} <> up, path}

# a walker's frame is its view's
law gw.frame_view:
  for st: Shake.St
  {gw.frame(st) == gw.vframe(view(st)) : Frame}

def gw.frame_view(st):
  match st:
    case Shake.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      {==}
