# proofs of laws/BindingsComeFromWords.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/walk.bend as Walk
import ../src/grow.bend as Grow
import ../laws/BindingsComeFromWords.bend as Laws
import ../laws/WalkAppend.bend as L1
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/FinishedWalker.bend as M1
import ./lemmas/NameAppend.bend as M2
import ./lemmas/WalkSteps.bend as M3

# ---- laws/BindingsComeFromWords.bend: every value bound is a piece of a word, `true` or a default

# anything or true is true
def gv.or_t(bb: Bool) -> {Bool.or(bb, True{}) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# both halves of a true `and` are true
def gv.and_tt(
  aa: Bool,
  +bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, bb) == True{} : Bool}, Walk.wk.false_true(ha))

# the left half of a true `and`
def gv.and_l(aa: Bool, bb: Bool, +hh: {Bool.and(aa, bb) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Walk.wk.false_true(hh))

# the right half of a true `and`
def gv.and_r(aa: Bool, +bb: Bool, +hh: {Bool.and(aa, bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      Empty.absurd({bb == True{} : Bool}, Walk.wk.false_true(hh))

# a word is what is left of itself
def gv.ends_self(ww: String) -> {D1.ends(ww, ww) == True{} : Bool}:
  match ww:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      ee = Equal.sym(Bool, String.eq(SCon{hh, tt}, SCon{hh, tt}), True{}, Eq.string_eq_self(SCon{hh, tt}))
      %ee : {Bool.or(_, D1.ends(tt, SCon{hh, tt})) == True{} : Bool}
      {==}

# what is left of a word's tail is left of the word
def gv.ends_tail(
  +cc: Char,
  +tt: String,
  +vv: String,
  +hh: {D1.ends(tt, vv) == True{} : Bool}
) -> {D1.ends(SCon{cc, tt}, vv) == True{} : Bool}:
  ee = Equal.sym(Bool, D1.ends(tt, vv), True{}, hh)
  %ee : {Bool.or(String.eq(vv, SCon{cc, tt}), _) == True{} : Bool}
  gv.or_t(String.eq(vv, SCon{cc, tt}))

# dropping nothing leaves the string
def gv.drop0(ss: String) -> {String.drop(ss, 0n) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_c, _t}:
      {==}

# whether every piece of `ww` is a piece of one of the words
def gv.sufs(ww: String, +ws: List<&2, String>) -> Bool:
  match ww:
    case SNil{}:
      D1.piece(ws, "")
    case SCon{+cc, +tt}:
      Bool.and(D1.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws))

# every piece of `ww` is a piece of one of the words
def gv.In(+ww: String, +ws: List<&2, String>) -> Type:
  {gv.sufs(ww, ws) == True{} : Bool}

# a word's tail is within the words when the word is
def gv.in_tail(+cc: Char, +tt: String, +ws: List<&2, String>, hh: gv.In(SCon{cc, tt}, ws)) -> gv.In(tt, ws):
  gv.and_r(D1.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws), hh)

# a word with chars dropped from its front is within the words when it is
def gv.in_drop(ww: String, kk: Nat, +ws: List<&2, String>, hh: gv.In(ww, ws)) -> gv.In(String.drop(ww, kk), ws):
  match ww kk:
    case SNil{} _:
      hh
    case SCon{+cc, +tt} 0n:
      hh
    case SCon{+cc, +tt} 1n+pp:
      gv.in_drop(tt, pp, ws, gv.in_tail(cc, tt, ws, hh))

# a word within the words is a piece of them
def gv.in_piece(ww: String, +ws: List<&2, String>, hh: gv.In(ww, ws)) -> {D1.piece(ws, ww) == True{} : Bool}:
  match ww:
    case SNil{}:
      hh
    case SCon{+cc, +tt}:
      gv.and_l(D1.piece(ws, SCon{cc, tt}), gv.sufs(tt, ws), hh)

# what is left of a word once some chars are dropped is left of it
def gv.ends_drop(ww: String, kk: Nat) -> {D1.ends(ww, String.drop(ww, kk)) == True{} : Bool}:
  match ww kk:
    case SNil{} _:
      {==}
    case SCon{+cc, +tt} 0n:
      gv.ends_self(SCon{cc, tt})
    case SCon{+cc, +tt} 1n+(+pp):
      gv.ends_tail(cc, tt, String.drop(tt, pp), gv.ends_drop(tt, pp))

# what is left of a word of a list is a piece of the list
def gv.mid_piece(
  pre: List<&2, String>,
  +tok: String,
  +rest: List<&2, String>,
  +vv: String,
  +hv: {D1.ends(tok, vv) == True{} : Bool}
) -> {D1.piece(List.append(&2, String, pre, tok <> rest), vv) == True{} : Bool}:
  match pre:
    case Nil{}:
      ee = Equal.sym(Bool, D1.ends(tok, vv), True{}, hv)
      %ee : {Bool.or(_, D1.piece(rest, vv)) == True{} : Bool}
      {==}
    case Con{+pp, +pt}:
      ih = gv.mid_piece(pt, tok, rest, vv, hv)
      ee = Equal.sym(Bool, D1.piece(List.append(&2, String, pt, tok <> rest), vv), True{}, ih)
      %ee : {Bool.or(D1.ends(pp, vv), _) == True{} : Bool}
      gv.or_t(D1.ends(pp, vv))

# the tail of a string, empty for the empty one
def gv.tail(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{_c, tt}:
      tt

# whether a string is empty, as a type: the empty one is not a char in front
def gv.snil_ty(ss: String) -> Type:
  match ss:
    case SNil{}:
      Unit
    case SCon{_c, _t}:
      Empty

# the empty string is never a char in front of one
def gv.snil_scon(+cc: Char, +tt: String, ee: {SNil{} == SCon{cc, tt} : String}) -> Empty:
  %ee : gv.snil_ty(_)
  Unit{}

# dropping one more char leaves the tail of what was left
def gv.drop_succ(
  ww: String,
  kk: Nat,
  +cc: Char,
  +tt: String,
  +ee: {String.drop(ww, kk) == SCon{cc, tt} : String}
) -> {String.drop(ww, 1n+kk) == tt : String}:
  match ww kk:
    case SNil{} _:
      Empty.absurd({SNil{} == tt : String}, gv.snil_scon(cc, tt, ee))
    case SCon{+dd, +uu} 0n:
      Equal.trans(String, String.drop(uu, 0n), uu, tt, gv.drop0(uu),
        Equal.cong(String, String, ss => gv.tail(ss), SCon{dd, uu}, SCon{cc, tt}, ee))
    case SCon{+dd, +uu} 1n+pp:
      gv.drop_succ(uu, pp, cc, tt, ee)

# what is left of a word once some chars are dropped, named
def gv.ends_at(
  +tok: String,
  +kk: Nat,
  +xx: String,
  +ee: {String.drop(tok, kk) == xx : String}
) -> {D1.ends(tok, xx) == True{} : Bool}:
  %ee : {D1.ends(tok, _) == True{} : Bool}
  gv.ends_drop(tok, kk)

# every suffix of a word of a list is within the list
def gv.sufs_in(
  xx: String,
  +tok: String,
  +kk: Nat,
  +pre: List<&2, String>,
  +rest: List<&2, String>,
  +ee: {String.drop(tok, kk) == xx : String}
) -> gv.In(xx, List.append(&2, String, pre, tok <> rest)):
  match xx:
    case SNil{}:
      gv.mid_piece(pre, tok, rest, SNil{}, gv.ends_at(tok, kk, SNil{}, ee))
    case SCon{+cc, +tt}:
      gv.and_tt(D1.piece(List.append(&2, String, pre, tok <> rest), SCon{cc, tt}),
        gv.sufs(tt, List.append(&2, String, pre, tok <> rest)),
        gv.mid_piece(pre, tok, rest, SCon{cc, tt}, gv.ends_at(tok, kk, SCon{cc, tt}, ee)),
        gv.sufs_in(tt, tok, 1n+kk, pre, rest, gv.drop_succ(tok, kk, cc, tt, ee)))

# a word of a list is within it
def gv.in_mid(
  +pre: List<&2, String>,
  +tok: String,
  +rest: List<&2, String>
) -> gv.In(tok, List.append(&2, String, pre, tok <> rest)):
  gv.sufs_in(tok, tok, 0n, pre, rest, gv.drop0(tok))

# a value is `true` or a piece of one of the words
def gv.ok(+ws: List<&2, String>, +vv: String) -> Bool:
  Bool.or(String.eq(vv, "true"), D1.piece(ws, vv))

# a value within the words is one
def gv.ok_in(+ws: List<&2, String>, +vv: String, hh: gv.In(vv, ws)) -> {gv.ok(ws, vv) == True{} : Bool}:
  ee = Equal.sym(Bool, D1.piece(ws, vv), True{}, gv.in_piece(vv, ws, hh))
  %ee : {Bool.or(String.eq(vv, "true"), _) == True{} : Bool}
  gv.or_t(String.eq(vv, "true"))

# every binding's value is one
def gv.all(bs: List<&2, S.Bind>, +ws: List<&2, String>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Bind{_n, vv} = hh
      Bool.and(gv.ok(ws, vv), gv.all(tt, ws))

# every level's bindings' values are
def gv.ups(lvs: List<&2, S.Level>, +ws: List<&2, String>) -> Bool:
  match lvs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Level{_a, bs} = hh
      Bool.and(gv.all(bs, ws), gv.ups(tt, ws))

# every value a walker holds, at every level, is one
def gv.good(st: S.St, +ws: List<&2, String>) -> Bool:
  S.St{_m, _a, up, _s, _p, binds, _o, _r, _n} = st
  Bool.and(gv.all(binds, ws), gv.ups(up, ws))

# a walker whose values all are
def gv.G(st: S.St, +ws: List<&2, String>) -> Type:
  {gv.good(st, ws) == True{} : Bool}

# a value, when there is one, is
def gv.mok(mv: Maybe<&2, String>, +ws: List<&2, String>) -> Bool:
  match mv:
    case None{}:
      True{}
    case Some{vv}:
      gv.ok(ws, vv)

# the value of a name and value cut, when there is one, is
def gv.pok(nv: String & Maybe<&2, String>, +ws: List<&2, String>) -> Bool:
  (_n, mv) = nv
  gv.mok(mv, ws)

# a walker that keeps its bindings and the levels above
def gv.keep(
  +binds: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +ws: List<&2, String>,
  +hb: {gv.all(binds, ws) == True{} : Bool},
  +hu: {gv.ups(up, ws) == True{} : Bool}
) -> {Bool.and(gv.all(binds, ws), gv.ups(up, ws)) == True{} : Bool}:
  gv.and_tt(gv.all(binds, ws), gv.ups(up, ws), hb, hu)

# the values a walker holds, as a type
def gv.B(+binds: List<&2, S.Bind>, +ws: List<&2, String>) -> Type:
  {gv.all(binds, ws) == True{} : Bool}

# the values of the levels above, as a type
def gv.U(+up: List<&2, S.Level>, +ws: List<&2, String>) -> Type:
  {gv.ups(up, ws) == True{} : Bool}

# a binding of a value that is one
def gv.put(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.and_tt(Bool.and(gv.ok(ws, val), gv.all(binds, ws)), gv.ups(up, ws),
    gv.and_tt(gv.ok(ws, val), gv.all(binds, ws), hv, hb), hu)

# a value bound when allowed
def gv.choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  match ok:
    case True{}:
      gv.put(name, val, args, up, subs, path, binds, pos, raw, seen, ws, hv, hb, hu)
    case False{}:
      gv.keep(binds, up, ws, hb, hu)

# an option's value
def gv.opt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hv: {gv.ok(ws, val) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.choice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos,
    raw, seen, ws, hv, hb, hu)

# a flag binds `true`
def gv.flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gv.put(name, "true", args, up, subs, path, binds, pos, raw, seen, ws, {==}, hb, hu)
    case Some{_v}:
      gv.keep(binds, up, ws, hb, hu)

# an option: its value now, or it waits
def gv.opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{vv}:
      gv.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# the once-check keeps the walker's values
def gv.once(
  again: Bool,
  st: S.St,
  +name: String,
  +path: List<&2, String>,
  +ws: List<&2, String>,
  hg: gv.G(st, ws)
) -> gv.G(S.parse.once(again, st, name, path), ws):
  match again:
    case True{}:
      match st:
        case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
          hg
    case False{}:
      hg

# a found argument, by its kind
def gv.akind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match kk:
    case S.Flag{}:
      gv.once(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gv.flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen, ws, hb, hu))
    case S.Opt{}:
      gv.once(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gv.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu))
    case S.Many{}:
      gv.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)
    case S.Pos{}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Rest{}:
      gv.keep(binds, up, ws, hb, hu)

# a found argument, or an unknown flag
def gv.arg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          gv.akind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# an unknown long option: a request for help, or an unknown flag
def gv.lhelp(
  hit: Bool,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.help(hit, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match hit:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.keep(binds, up, ws, hb, hu)

# a long option the current command spells, or an unknown one
def gv.found(
  found: Maybe<&2, S.Arg>,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.found(found, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.lhelp(S.long_help(name, val, seen), orig, args, up, subs, path, binds, pos, raw, seen, ws, hb, hu)
    case Some{aa}:
      gv.arg(Some{aa}, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# a long option with a name
def gv.named(
  empty: Bool,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match empty:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.found(S.by_long(args, name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hm, hb, hu)

# a long option after the `=` cut
def gv.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hp: {gv.pok(nv, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match nv:
    case (+name, +val):
      gv.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hp, hb, hu)

# the `=` cut's value, when the `=` is here
def gv.cut_pick(
  eq: Bool,
  +acc: List<&2, Char>,
  +tt: List<&2, Char>,
  rest: String & Maybe<&2, String>,
  +ws: List<&2, String>,
  +hr: {gv.pok(rest, ws) == True{} : Bool},
  +ht: {gv.ok(ws, String.from_list(tt)) == True{} : Bool}
) -> {gv.pok(S.cut_eq.pick(eq, acc, tt, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      ht
    case False{}:
      hr

# the `=` cut's value is within the words when the body is
def gv.cut_go(
  cs: List<&2, Char>,
  +acc: List<&2, Char>,
  +ws: List<&2, String>,
  hh: gv.In(String.from_list(cs), ws)
) -> {gv.pok(S.cut_eq.go(cs, acc), ws) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+cc, +tt}:
      +hi = {gv.in_tail(cc, String.from_list(tt), ws, hh) : {gv.sufs(String.from_list(tt), ws) == True{} : Bool}}
      gv.cut_pick(Char.is_eq(cc, '='), acc, tt, S.cut_eq.go(tt, cc <> acc), ws, gv.cut_go(tt, cc <> acc, ws, hi),
        gv.ok_in(ws, String.from_list(tt), hi))

# a string read as chars and back is itself
def gv.round(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(String, String, xs => SCon{hh, xs}, String.from_list(String.to_list(tt)), tt, gv.round(tt))

# a long option body within the words
def gv.long(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hh: gv.In(body, ws),
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  ee = Equal.sym(String, String.from_list(String.to_list(body)), body, gv.round(body))
  hr = {%ee : gv.In(_, ws)
    hh : gv.In(String.from_list(String.to_list(body)), ws)}
  gv.cut(S.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen, ws,
    gv.cut_go(String.to_list(body), [], ws, hr), hb, hu)

# a flag letter's value: the rest after `=`
def gv.cflag(
  eq: Bool,
  +rest: String,
  +ws: List<&2, String>,
  hh: gv.In(rest, ws)
) -> {gv.mok(S.cluster.val.flag(eq, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      gv.ok_in(ws, rest, hh)
    case False{}:
      {==}

# the rest of the cluster, when there is any
def gv.crest(
  rest: String,
  +ws: List<&2, String>,
  hh: gv.In(rest, ws)
) -> {gv.mok(Bool.pick(Maybe<&2, String>, String.is_empty(rest), None{}, Some{rest}), ws) == True{} : Bool}:
  match rest:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      gv.ok_in(ws, SCon{cc, tt}, hh)

# an option letter's value: after one `=`, or the rest
def gv.sval(
  eq: Bool,
  +rest: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool}
) -> {gv.mok(S.short_of.val(eq, rest), ws) == True{} : Bool}:
  match eq:
    case True{}:
      gv.ok_in(ws, String.drop(rest, 1n), gv.in_drop(rest, 1n, ws, hh))
    case False{}:
      gv.crest(rest, ws, hh)

# a letter's value is within the words when the rest of the cluster is
def gv.cval(
  found: Maybe<&2, S.Arg>,
  +rest: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool}
) -> {gv.mok(S.cluster.val(found, rest), ws) == True{} : Bool}:
  match found:
    case None{}:
      {==}
    case Some{aa}:
      match aa:
        case S.Arg{_n, _s, _l, kind, _h, _r, _d, _c}:
          match kind:
            case S.Flag{}:
              gv.cflag(String.starts_with(rest, "="), rest, ws, hh)
            case S.Opt{}:
              gv.sval(String.starts_with(rest, "="), rest, ws, hh)
            case S.Many{}:
              gv.sval(String.starts_with(rest, "="), rest, ws, hh)
            case S.Pos{}:
              {==}
            case S.Rest{}:
              {==}

# one letter, by the walker's mode
def gv.capply_mode(
  mode: S.Mode,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.cluster.apply.mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Free{}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)
    case S.Need{_n}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)
    case S.Help{}:
      gv.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hu)

# one letter against the walker
def gv.capply(
  st: S.St,
  +cc: Char,
  +rest: String,
  +orig: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster.apply(st, cc, rest, orig), ws):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gv.capply_mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_l(gv.all(binds, ws), gv.ups(up, ws), hg), gv.and_r(gv.all(binds, ws), gv.ups(up, ws), hg))

# one letter, unless the cluster has ended
def gv.letter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster.letter(done, cc, rest, orig, st), ws):
  match done:
    case True{}:
      hg
    case False{}:
      gv.capply(st, cc, rest, orig, ws, hh, hg)

# every letter of a cluster within the words
def gv.cluster(
  body: String,
  +orig: String,
  +st: S.St,
  +done: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.cluster(body, orig, st, done), ws):
  match body:
    case SNil{}:
      hg
    case SCon{+cc, +rest}:
      +hr = {gv.in_tail(cc, rest, ws, hh) : {gv.sufs(rest, ws) == True{} : Bool}}
      gv.cluster(rest, orig, S.cluster.letter(done, cc, rest, orig, st), S.cluster.done(done, cc, rest, st), ws, hr,
        gv.letter(done, cc, rest, orig, st, ws, hr, hg))

# a short option body within the words: a request for help, or a cluster
def gv.sgo(
  hit: Bool,
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hb: {gv.all(binds, ws) == True{} : Bool},
  +hu: {gv.ups(up, ws) == True{} : Bool}
) -> gv.G(S.parse.take_short.go(hit, body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match hit:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.cluster(body, orig, S.St{S.Free{}, args, up, subs, path, binds, pos, raw, seen}, False{}, ws, hh,
        gv.keep(binds, up, ws, hb, hu))

# a short option body within the words
def gv.short(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_short(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.sgo(S.short_help(body, args, seen), body, orig, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)

# a positional binds the word
def gv.take_pos(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  pos: List<&2, S.Arg>,
  +raw: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), ws):
  match pos:
    case Nil{}:
      gv.keep(binds, up, ws, hb, hu)
    case Con{hp, +tt}:
      match hp:
        case S.Arg{+name, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          gv.choice(S.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt), raw, True{}, ws, gv.ok_in(ws, tok, hh), hb, hu)

# entering a subcommand moves the bindings up a level
def gv.enter(
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.enter(ss, args, up, path, binds), ws):
  match ss:
    case S.Sub{_n, _a, _g, _c}:
      gv.keep(binds, up, ws, hb, hu)

# a subcommand entered, or a missing positional
def gv.enter_or(
  miss: Maybe<&2, String>,
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), ws):
  match miss:
    case None{}:
      gv.enter(ss, args, up, path, binds, ws, hb, hu)
    case Some{_n}:
      gv.keep(binds, up, ws, hb, hu)

# a word: a subcommand, or a positional
def gv.word_go(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.take_pos(tok, args, up, subs, path, binds, pos, raw, ws, hh, hb, hu)
    case Some{ss}:
      gv.enter_or(S.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen, ws, hb, hu)

# a word
def gv.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.word_go(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)

# `-` alone is a word; otherwise a cluster
def gv.short_go(
  alone: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), ws):
  match alone:
    case True{}:
      gv.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hu)
    case False{}:
      gv.short(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 1n, ws, hh), hb, hu)

# a short option or a word
def gv.step_short(
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match dash:
    case True{}:
      gv.short_go(String.is_empty(String.drop(tok, 1n)), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)
    case False{}:
      gv.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hu)

# a long option, a short one, or a word
def gv.kind_go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match long:
    case True{}:
      gv.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 2n, ws, hh), hb, hu)
    case False{}:
      gv.step_short(dash, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# a word by its shape
def gv.skind(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.kind(tok, args, up, subs, path, binds, pos, seen), ws):
  gv.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds, pos, seen,
    ws,
    hh, hb, hu)

# `help` starts a help path, keeping the bindings
def gv.help(
  hit: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), ws):
  match hit:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.skind(tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# `--` switches to positionals, keeping the bindings
def gv.end(
  end: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), ws):
  match end:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen, ws, hh,
        hb, hu)

# after `--` a word is a positional
def gv.raw(
  raw: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), ws):
  match raw:
    case True{}:
      gv.take_pos(tok, args, up, subs, path, binds, pos, True{}, ws, hh, hb, hu)
    case False{}:
      gv.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# a pending option binds the word
def gv.need(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match flag:
    case True{}:
      gv.keep(binds, up, ws, hb, hu)
    case False{}:
      gv.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen, ws, gv.ok_in(ws, tok, hh), hb, hu)

# a word of a help path keeps the bindings
def gv.help_path(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  _hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.help_path(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gv.keep(binds, up, ws, hb, hu)
    case Some{ss}:
      match ss:
        case S.Sub{_n, _a, _g, _c}:
          gv.keep(binds, up, ws, hb, hu)

# one word, by the walker's mode
def gv.mode(
  mode: S.Mode,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  hb: gv.B(binds, ws),
  hu: gv.U(up, ws)
) -> gv.G(S.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
      gv.keep(binds, up, ws, hb, hu)
    case S.Need{name}:
      gv.need(S.looks_flag(tok), name, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)
    case S.Help{}:
      gv.help_path(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hu)
    case S.Free{}:
      gv.raw(raw, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hu)

# one word within the words keeps every value a walker holds one
def gv.step(
  +tok: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hg: {gv.good(st, ws) == True{} : Bool}
) -> gv.G(S.parse.step(tok, st), ws):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gv.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_l(gv.all(binds, ws), gv.ups(up, ws), hg), gv.and_r(gv.all(binds, ws), gv.ups(up, ws), hg))

# a walker's values, from one list of words to an equal one
def gv.tr(
  st: S.St,
  +aa: List<&2, String>,
  +bb: List<&2, String>,
  +ee: {aa == bb : List<&2, String>},
  +hg: {gv.good(st, bb) == True{} : Bool}
) -> {gv.good(st, aa) == True{} : Bool}:
  e2 = Equal.sym(List<&2, String>, aa, bb, ee)
  %e2 : {gv.good(st, _) == True{} : Bool}
  hg

# walking the words after `pre` keeps every value one of the words' pieces
def gv.walk(
  tt: List<&2, String>,
  +pre: List<&2, String>,
  +st: S.St,
  +hg: {gv.good(st, List.append(&2, String, pre, tt)) == True{} : Bool}
) -> {gv.good(S.parse.walk(tt, st), List.append(&2, String, pre, tt)) == True{} : Bool}:
  match tt:
    case Nil{}:
      hg
    case Con{+tok, +rest}:
      +ll = List.append(&2, String, pre, tok <> rest)
      +mm = List.append(&2, String, List.append(&2, String, pre, [tok]), rest)
      +ee = {M2.sc.app(pre, [tok], rest) : {mm == ll : List<&2, String>}}
      g1 = gv.step(tok, st, ll, gv.in_mid(pre, tok, rest), hg)
      gw = gv.walk(rest, List.append(&2, String, pre, [tok]), S.parse.step(tok, st),
        gv.tr(S.parse.step(tok, st), mm, ll, ee, g1))
      gv.tr(S.parse.walk(rest, S.parse.step(tok, st)), ll, mm, Equal.sym(List<&2, String>, mm, ll, ee), gw)

# a fresh walker holds no values
def gv.start(spec: Shake.Cli, +ws: List<&2, String>) -> {gv.good(S.parse.start(spec), ws) == True{} : Bool}:
  match spec:
    case S.Cli{_n, _a, _v, _g, _s}:
      {==}

# the values of a frame's levels
def gv.fups(fr: Grow.Frame, +ws: List<&2, String>) -> Bool:
  Grow.Frame{lvs, _p} = fr
  gv.ups(lvs, ws)

# a walker's frame holds its values
def gv.frame(
  st: S.St,
  +ws: List<&2, String>,
  hg: {gv.good(st, ws) == True{} : Bool}
) -> {gv.fups(Grow.gw.frame(st), ws) == True{} : Bool}:
  match st:
    case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      hg

# a level in the middle of a list of levels whose values all are
def gv.ups_mid(
  qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +ws: List<&2, String>,
  +hh: {gv.ups(List.append(&2, S.Level, qs, S.Level{args, bs} <> up), ws) == True{} : Bool}
) -> {gv.all(bs, ws) == True{} : Bool}:
  match qs:
    case Nil{}:
      gv.and_l(gv.all(bs, ws), gv.ups(up, ws), hh)
    case Con{qq, +qt}:
      match qq:
        case S.Level{_a, +qb}:
          gv.ups_mid(qt, args, bs, up, ws,
            gv.and_r(gv.all(qb, ws), gv.ups(List.append(&2, S.Level, qt, S.Level{args, bs} <> up), ws), hh))

# `true` or a piece is given
def gv.or3(
  ee: Bool,
  pp: Bool,
  +dd: Bool,
  +hh: {Bool.or(ee, pp) == True{} : Bool}
) -> {Bool.or(ee, Bool.or(pp, dd)) == True{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      match pp:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({Bool.or(False{}, Bool.or(False{}, dd)) == True{} : Bool}, Walk.wk.false_true(hh))

# a list of values that all are one is given
def gv.all_given(
  bs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hh: {gv.all(bs, ws) == True{} : Bool}
) -> {Laws.all_given(bs, ws, args) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Bind{+nn, +vv}:
          gv.and_tt(D1.given(ws, args, S.Bind{nn, vv}), Laws.all_given(tt, ws, args),
            gv.or3(String.eq(vv, "true"), D1.piece(ws, vv), D1.is_default(args, nn, vv),
              gv.and_l(gv.ok(ws, vv), gv.all(tt, ws), hh)),
            gv.all_given(tt, ws, args, gv.and_r(gv.ok(ws, vv), gv.all(tt, ws), hh)))

# a default of more arguments is still one
def gv.dmono(
  ee: Bool,
  pp: Bool,
  +xx: Bool,
  dd: Bool,
  +hh: {Bool.or(ee, Bool.or(pp, dd)) == True{} : Bool}
) -> {Bool.or(ee, Bool.or(pp, Bool.or(xx, dd))) == True{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      match pp:
        case True{}:
          {==}
        case False{}:
          e2 = Equal.sym(Bool, dd, True{}, hh)
          %e2 : {Bool.or(xx, _) == True{} : Bool}
          gv.or_t(xx)

# bindings given against some arguments are given against more
def gv.given_mono(
  xs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {Laws.all_given(xs, ws, tt) == True{} : Bool}
) -> {Laws.all_given(xs, ws, aa <> tt) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +xt}:
      match hd:
        case S.Bind{+nn, +vv}:
          match aa:
            case S.Arg{+an, +sh, +lo, +kind, +hp, +req, S.Fallback{+ev, +ad}, +cs}:
              gv.and_tt(D1.given(ws, S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, ad}, cs} <> tt, S.Bind{nn, vv}),
                Laws.all_given(xt, ws, S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, ad}, cs} <> tt),
                gv.dmono(String.eq(vv, "true"), D1.piece(ws, vv),
                  Bool.and(String.eq(an, nn), D1.default_is(ad, vv)), D1.is_default(tt, nn, vv),
                  gv.and_l(D1.given(ws, tt, S.Bind{nn, vv}), Laws.all_given(xt, ws, tt), hh)),
                gv.given_mono(xt, ws, S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, ad}, cs}, tt,
                  gv.and_r(D1.given(ws, tt, S.Bind{nn, vv}), Laws.all_given(xt, ws, tt), hh)))

# an argument's own default is given
def gv.dself(
  +ee: Bool,
  +pp: Bool,
  +nn: String,
  +vv: String,
  dd: Bool
) -> {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(String.eq(nn, nn), String.eq(vv, vv)), dd))) == True{} : Bool}:
  e1 = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  e2 = Equal.sym(Bool, String.eq(vv, vv), True{}, Eq.string_eq_self(vv))
  e3 = Equal.sym(Bool, Bool.or(pp, True{}), True{}, gv.or_t(pp))
  %e1 : {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(_, String.eq(vv, vv)), dd))) == True{} : Bool}
  %e2 : {Bool.or(ee, Bool.or(pp, Bool.or(Bool.and(True{}, _), dd))) == True{} : Bool}
  %e3 : {Bool.or(ee, _) == True{} : Bool}
  gv.or_t(ee)

# a default goes in front when its name is unbound
def gv.fone(
  skip: Bool,
  +nn: String,
  +vv: String,
  +rr: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hr: {Laws.all_given(rr, ws, args) == True{} : Bool},
  +hd: {D1.given(ws, args, S.Bind{nn, vv}) == True{} : Bool}
) -> {Laws.all_given(S.fill.one(skip, nn, vv, rr), ws, args) == True{} : Bool}:
  match skip:
    case True{}:
      hr
    case False{}:
      gv.and_tt(D1.given(ws, args, S.Bind{nn, vv}), Laws.all_given(rr, ws, args), hd, hr)

# the defaults filled in are the arguments' own
def gv.fill(
  args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +hh: {gv.all(bs, ws) == True{} : Bool}
) -> {Laws.all_given(S.fill.args(args, bs), ws, args) == True{} : Bool}:
  match args:
    case Nil{}:
      gv.all_given(bs, ws, [], hh)
    case Con{aa, +tt}:
      match aa:
        case S.Arg{+an, +sh, +lo, +kind, +hp, +req, S.Fallback{+ev, ad}, +cs}:
          match ad:
            case None{}:
              gv.given_mono(S.fill.args(tt, bs), ws, S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, None{}}, cs}, tt,
                gv.fill(tt, bs, ws, hh))
            case Some{+dv}:
              gv.fone(S.bound(S.fill.args(tt, bs), an), an, dv, S.fill.args(tt, bs), ws,
                S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, Some{dv}}, cs} <> tt,
                gv.given_mono(S.fill.args(tt, bs), ws, S.Arg{an, sh, lo, kind, hp, req, S.Fallback{ev, Some{dv}},
                    cs}, tt,
                  gv.fill(tt, bs, ws, hh)),
                gv.dself(String.eq(dv, "true"), D1.piece(ws, dv), an, dv, D1.is_default(tt, an, dv)))

# reversed bindings are given when they are
def gv.rev_given(
  xs: List<&2, S.Bind>,
  +acc: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hx: {Laws.all_given(xs, ws, args) == True{} : Bool},
  +ha: {Laws.all_given(acc, ws, args) == True{} : Bool}
) -> {Laws.all_given(List.reverse.go(&2, S.Bind, xs, acc), ws, args) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+hd, +tt}:
      gv.rev_given(tt, hd <> acc, ws, args,
        gv.and_r(D1.given(ws, args, hd), Laws.all_given(tt, ws, args), hx),
        gv.and_tt(D1.given(ws, args, hd), Laws.all_given(acc, ws, args),
          gv.and_l(D1.given(ws, args, hd), Laws.all_given(tt, ws, args), hx), ha))

# the bindings of a finished walker's level at `path` all are one
def gv.level(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +qs: List<&2, S.Level>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +ms: List<&2, String>,
  h_fr: M1.fin.Framed(spec, ws, qs, args, bs, up, path, ms)
) -> {gv.all(bs, ws) == True{} : Bool}:
  +fs = S.parse.walk(ws, S.parse.start(spec))
  +fr = {Grow.Frame{List.append(&2, S.Level, qs, S.Level{args, bs} <> up), List.append(&2, String, path, ms)}
    : Grow.Frame}
  fg = gv.frame(fs, ws, gv.walk(ws, [], S.parse.start(spec), gv.start(spec, ws)))
  gv.ups_mid(qs, args, bs, up, ws,
    Equal.trans(Bool, gv.fups(fr, ws), gv.fups(Grow.gw.frame(fs), ws), True{},
      Equal.cong(Grow.Frame, Bool, ff => gv.fups(ff, ws), fr, Grow.gw.frame(fs),
        Equal.sym(Grow.Frame, Grow.gw.frame(fs), fr, h_fr)),
      fg))

def Laws.values_given(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len):
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  ea = Equal.sym(Maybe<&2, S.Matched>, S.at(found, path), Some{S.matched.build(f0 <> rq, ms)},
    M1.fin.at(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len))
  eo = Equal.sym(List<&2, S.Bind>, S.own(S.matched.build(f0 <> rq, ms)),
    List.reverse(&2, S.Bind, S.fill.args(args, bs)), Grow.gw.own_build(f0, rq, ms))
  %ea : {Laws.given_at.go(_, ws, args) == Some{True{}} : Maybe<&2, Bool>}
  %eo : {Some{Laws.all_given(_, ws, args)} == Some{True{}} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, bb => Some{bb},
    Laws.all_given(List.reverse(&2, S.Bind, S.fill.args(args, bs)), ws, args), True{},
    gv.rev_given(S.fill.args(args, bs), [], ws, args,
      gv.fill(args, bs, ws, gv.level(spec, ws, qs, args, bs, up, path, ms, h_fr)), {==}))

# ---- laws/BindingsComeFromWords.bend: every value a command binds is named after one of its
# arguments and is a piece of the words read while it was current

# an argument's name
def gn.name(aa: S.Arg) -> String:
  S.Arg{nn, _s, _l, _k, _h, _r, _d, _c} = aa
  nn

# whether a binding is named after one of `args` and its value is `true` or a
# piece of one of the words
def gn.nok(+args: List<&2, S.Arg>, +ws: List<&2, String>, bb: S.Bind) -> Bool:
  S.Bind{+nn, +vv} = bb
  Bool.and(Laws.has_arg(args, nn), gv.ok(ws, vv))

# whether every binding is
def gn.all(bs: List<&2, S.Bind>, +args: List<&2, S.Arg>, +ws: List<&2, String>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      Bool.and(gn.nok(args, ws, hh), gn.all(tt, args, ws))

# whether every pending positional is one of `args`
def gn.pin(pos: List<&2, S.Arg>, +args: List<&2, S.Arg>) -> Bool:
  match pos:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      S.Arg{+nn, _s, _l, _k, _h, _r, _d, _c} = hh
      Bool.and(Laws.has_arg(args, nn), gn.pin(tt, args))

# whether an option waiting for its value is one of `args`
def gn.min(mode: S.Mode, +args: List<&2, S.Arg>) -> Bool:
  match mode:
    case S.Need{nn}:
      Laws.has_arg(args, nn)
    case S.Free{}:
      True{}
    case S.Help{}:
      True{}
    case S.Dead{_e}:
      True{}

# a walker whose waiting option and pending positionals are its command's own
def gn.wf(st: S.St) -> Bool:
  S.St{mode, +args, _g, _s, _p, _b, pos, _r, _n} = st
  Bool.and(gn.min(mode, args), gn.pin(pos, args))

# that, and every binding of its command is named after one of its arguments
# and is `true` or a piece of the words
def gn.good(st: S.St, +ws: List<&2, String>) -> Bool:
  S.St{mode, +args, _g, _s, _p, binds, pos, _r, _n} = st
  Bool.and(Bool.and(gn.min(mode, args), gn.pin(pos, args)), gn.all(binds, args, ws))

# a walker that is good, as a type
def gn.G(st: S.St, +ws: List<&2, String>) -> Type:
  {gn.good(st, ws) == True{} : Bool}

# a walker that keeps its command, its bindings and its positionals, free
def gn.keep(
  +args: List<&2, S.Arg>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +ws: List<&2, String>,
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> {Bool.and(gn.pin(pos, args), gn.all(binds, args, ws)) == True{} : Bool}:
  gv.and_tt(gn.pin(pos, args), gn.all(binds, args, ws), hp, hb)

# `x` or something true is true
def gn.or_rt(+xx: Bool, yy: Bool, +hh: {yy == True{} : Bool}) -> {Bool.or(xx, yy) == True{} : Bool}:
  ee = Equal.sym(Bool, yy, True{}, hh)
  %ee : {Bool.or(xx, _) == True{} : Bool}
  gv.or_t(xx)

# an argument is one of a list it heads
def gn.has_self(aa: S.Arg, +tt: List<&2, S.Arg>) -> {Laws.has_arg(aa <> tt, gn.name(aa)) == True{} : Bool}:
  match aa:
    case S.Arg{+nn, _s, _l, _k, _h, _r, _d, _c}:
      ee = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
      %ee : {Bool.or(_, Laws.has_arg(tt, nn)) == True{} : Bool}
      {==}

# one of some arguments is one of more
def gn.has_mono(
  aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +nn: String,
  +hh: {Laws.has_arg(tt, nn) == True{} : Bool}
) -> {Laws.has_arg(aa <> tt, nn) == True{} : Bool}:
  match aa:
    case S.Arg{+an, _s, _l, _k, _h, _r, _d, _c}:
      gn.or_rt(String.eq(an, nn), Laws.has_arg(tt, nn), hh)

# pending positionals of some arguments are pending of more
def gn.pin_mono(
  xs: List<&2, S.Arg>,
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {gn.pin(xs, tt) == True{} : Bool}
) -> {gn.pin(xs, aa <> tt) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{xx, +xt}:
      match xx:
        case S.Arg{+xn, _s, _l, _k, _h, _r, _d, _c}:
          gv.and_tt(Laws.has_arg(aa <> tt, xn), gn.pin(xt, aa <> tt),
            gn.has_mono(aa, tt, xn, gv.and_l(Laws.has_arg(tt, xn), gn.pin(xt, tt), hh)),
            gn.pin_mono(xt, aa, tt, gv.and_r(Laws.has_arg(tt, xn), gn.pin(xt, tt), hh)))

# a positional kept pending, or not
def gn.pin_put(
  keep: Bool,
  aa: S.Arg,
  +rest: List<&2, S.Arg>,
  +tt: List<&2, S.Arg>,
  +hr: {gn.pin(rest, aa <> tt) == True{} : Bool}
) -> {gn.pin(S.pos_of.put(keep, aa, rest), aa <> tt) == True{} : Bool}:
  match keep:
    case True{}:
      match aa:
        case S.Arg{+nn, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          gv.and_tt(Laws.has_arg(S.Arg{nn, sh, lo, kind, hl, req, dd, cs} <> tt, nn),
            gn.pin(rest, S.Arg{nn, sh, lo, kind, hl, req, dd, cs} <> tt),
            gn.has_self(S.Arg{nn, sh, lo, kind, hl, req, dd, cs}, tt), hr)
    case False{}:
      hr

# the positionals of some arguments are among them
def gn.pin_of(args: List<&2, S.Arg>) -> {gn.pin(S.pos_of(args), args) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+aa, +tt}:
      gn.pin_put(S.pos.is(aa), aa, S.pos_of(tt), tt, gn.pin_mono(S.pos_of(tt), aa, tt, gn.pin_of(tt)))

# whether a found argument is one of `args`
def gn.fok(found: Maybe<&2, S.Arg>, +args: List<&2, S.Arg>) -> Bool:
  match found:
    case None{}:
      True{}
    case Some{aa}:
      Laws.has_arg(args, gn.name(aa))

# a found argument among some is among more
def gn.fok_mono(
  mm: Maybe<&2, S.Arg>,
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {gn.fok(mm, tt) == True{} : Bool}
) -> {gn.fok(mm, aa <> tt) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{xx}:
      gn.has_mono(aa, tt, gn.name(xx), hh)

# the argument found by a long spelling, when the head matches or not
def gn.fok_long_at(
  hit: Bool,
  +hh: S.Arg,
  +tt: List<&2, S.Arg>,
  +rest: Maybe<&2, S.Arg>,
  +hr: {gn.fok(rest, tt) == True{} : Bool}
) -> {gn.fok(S.by_long.at(hit, hh, rest), hh <> tt) == True{} : Bool}:
  match hit:
    case True{}:
      gn.has_self(hh, tt)
    case False{}:
      gn.fok_mono(rest, hh, tt, hr)

# the argument found by a long spelling is one of them
def gn.fok_long(args: List<&2, S.Arg>, +name: String) -> {gn.fok(S.by_long(args, name), args) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      gn.fok_long_at(S.by_long.hit(hh, name), hh, tt, S.by_long(tt, name), gn.fok_long(tt, name))

# the argument found by a short spelling, when the head matches or not
def gn.fok_short_at(
  hit: Bool,
  +hh: S.Arg,
  +tt: List<&2, S.Arg>,
  +rest: Maybe<&2, S.Arg>,
  +hr: {gn.fok(rest, tt) == True{} : Bool}
) -> {gn.fok(S.by_short.at(hit, hh, rest), hh <> tt) == True{} : Bool}:
  match hit:
    case True{}:
      gn.has_self(hh, tt)
    case False{}:
      gn.fok_mono(rest, hh, tt, hr)

# the argument found by a short spelling is one of them
def gn.fok_short(args: List<&2, S.Arg>, +name: String) -> {gn.fok(S.by_short(args, name), args) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      gn.fok_short_at(S.by_short.hit(hh, name), hh, tt, S.by_short(tt, name), gn.fok_short(tt, name))

# a binding named after one of the arguments, of a value that is one
def gn.put(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hv: {gv.ok(ws, val) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gv.and_tt(gn.pin(pos, args), Bool.and(gn.nok(args, ws, S.Bind{name, val}), gn.all(binds, args, ws)), hp,
    gv.and_tt(gn.nok(args, ws, S.Bind{name, val}), gn.all(binds, args, ws),
      gv.and_tt(Laws.has_arg(args, name), gv.ok(ws, val), hn, hv), hb))

# a value bound when allowed
def gn.choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hv: {gv.ok(ws, val) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  match ok:
    case True{}:
      gn.put(name, val, args, up, subs, path, binds, pos, raw, seen, ws, hn, hv, hb, hp)
    case False{}:
    gn.keep(args, binds, pos, ws, hb, hp)

# an option's value
def gn.opt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hv: {gv.ok(ws, val) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), ws):
  gn.choice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos,
    raw, seen, ws, hn, hv, hb, hp)

# a flag binds `true`
def gn.flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gn.put(name, "true", args, up, subs, path, binds, pos, raw, seen, ws, hn, {==}, hb, hp)
    case Some{_v}:
    gn.keep(args, binds, pos, ws, hb, hp)

# an option: its value now, or it waits, one of the arguments
def gn.opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hm: {gv.mok(val, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), ws):
  match val:
    case None{}:
      gv.and_tt(Bool.and(Laws.has_arg(args, name), gn.pin(pos, args)), gn.all(binds, args, ws),
        gv.and_tt(Laws.has_arg(args, name), gn.pin(pos, args), hn, hp), hb)
    case Some{vv}:
      gn.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen, ws, hn, hm, hb, hp)

# the once-check keeps a good walker good
def gn.once(
  again: Bool,
  st: S.St,
  +name: String,
  +path: List<&2, String>,
  +ws: List<&2, String>,
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> gn.G(S.parse.once(again, st, name, path), ws):
  match again:
    case True{}:
      match st:
        case S.St{+mode, +aa, _g, _s, _p, +bb, +oo, _r, _n}:
          gv.and_tt(gn.pin(oo, aa), gn.all(bb, aa, ws),
            gv.and_r(gn.min(mode, aa), gn.pin(oo, aa),
              gv.and_l(Bool.and(gn.min(mode, aa), gn.pin(oo, aa)), gn.all(bb, aa, ws), hg)),
            gv.and_r(Bool.and(gn.min(mode, aa), gn.pin(oo, aa)), gn.all(bb, aa, ws), hg))
    case False{}:
      hg

# a found argument, by its kind
def gn.akind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hm: {gv.mok(val, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match kk:
    case S.Flag{}:
      gn.once(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gn.flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen, ws, hn, hb, hp))
    case S.Opt{}:
      gn.once(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, ws, gn.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hn, hm, hb, hp))
    case S.Many{}:
      gn.opt(val, name, args, up, subs, path, binds, pos, raw, seen, ws, hn, hm, hb, hp)
    case S.Pos{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case S.Rest{}:
    gn.keep(args, binds, pos, ws, hb, hp)

# a found argument, or an unknown flag
def gn.arg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hf: {gn.fok(found, args) == True{} : Bool},
  +hm: {gv.mok(val, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          gn.akind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hf, hm, hb, hp)

# an unknown long option: a request for help, or an unknown flag
def gn.lhelp(
  hit: Bool,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_long.help(hit, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match hit:
    case True{}:
      gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.keep(args, binds, pos, ws, hb, hp)

# a long option the current command spells, or an unknown one
def gn.found(
  found: Maybe<&2, S.Arg>,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hf: {gn.fok(found, args) == True{} : Bool},
  +hm: {gv.mok(val, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_long.found(found, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gn.lhelp(S.long_help(name, val, seen), orig, args, up, subs, path, binds, pos, raw, seen, ws, hb, hp)
    case Some{aa}:
      gn.arg(Some{aa}, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hf, hm, hb, hp)

# a long option with a name
def gn.named(
  empty: Bool,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hm: {gv.mok(val, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match empty:
    case True{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.found(S.by_long(args, name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws,
        gn.fok_long(args, name), hm, hb, hp)

# a long option after the `=` cut
def gn.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hq: {gv.pok(nv, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match nv:
    case (+name, +val):
      gn.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, ws, hq, hb, hp)

# a long option body within the words
def gn.long(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  ee = Equal.sym(String, String.from_list(String.to_list(body)), body, gv.round(body))
  hr = {%ee : gv.In(_, ws)
    hh : gv.In(String.from_list(String.to_list(body)), ws)}
  gn.cut(S.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen, ws,
    gv.cut_go(String.to_list(body), [], ws, hr), hb, hp)

# one letter, by the walker's mode
def gn.capply_mode(
  mode: S.Mode,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.cluster.apply.mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case S.Free{}:
      gn.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gn.fok_short(args, SCon{cc, SNil{}}),
        gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hp)
    case S.Need{_n}:
      gn.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gn.fok_short(args, SCon{cc, SNil{}}),
        gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hp)
    case S.Help{}:
      gn.arg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, ws, gn.fok_short(args, SCon{cc, SNil{}}),
        gv.cval(S.by_short(args, SCon{cc, SNil{}}), rest, ws, hh), hb, hp)

# one letter against a good walker
def gn.capply(
  st: S.St,
  +cc: Char,
  +rest: String,
  +orig: String,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> gn.G(S.cluster.apply(st, cc, rest, orig), ws):
  match st:
    case S.St{+mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      gn.capply_mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_r(Bool.and(gn.min(mode, args), gn.pin(pos, args)), gn.all(binds, args, ws), hg),
        gv.and_r(gn.min(mode, args), gn.pin(pos, args),
          gv.and_l(Bool.and(gn.min(mode, args), gn.pin(pos, args)), gn.all(binds, args, ws), hg)))

# one letter, unless the cluster has ended
def gn.letter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(rest, ws) == True{} : Bool},
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> gn.G(S.cluster.letter(done, cc, rest, orig, st), ws):
  match done:
    case True{}:
      hg
    case False{}:
      gn.capply(st, cc, rest, orig, ws, hh, hg)

# every letter of a cluster within the words
def gn.cluster(
  body: String,
  +orig: String,
  +st: S.St,
  +done: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> gn.G(S.cluster(body, orig, st, done), ws):
  match body:
    case SNil{}:
      hg
    case SCon{+cc, +rest}:
      +hr = {gv.in_tail(cc, rest, ws, hh) : {gv.sufs(rest, ws) == True{} : Bool}}
      gn.cluster(rest, orig, S.cluster.letter(done, cc, rest, orig, st), S.cluster.done(done, cc, rest, st), ws, hr,
        gn.letter(done, cc, rest, orig, st, ws, hr, hg))

# a short option body within the words: a request for help, or a cluster
def gn.sgo(
  hit: Bool,
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_short.go(hit, body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  match hit:
    case True{}:
      gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.cluster(body, orig, S.St{S.Free{}, args, up, subs, path, binds, pos, raw, seen}, False{}, ws, hh,
        gn.keep(args, binds, pos, ws, hb, hp))

# a short option body within the words
def gn.short(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(body, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_short(body, orig, args, up, subs, path, binds, pos, raw, seen), ws):
  gn.sgo(S.short_help(body, args, seen), body, orig, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hp)

# a positional consumed, or kept when it is a rest
def gn.kpos(
  keep: Bool,
  aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +args: List<&2, S.Arg>,
  +hh: {gn.pin(aa <> tt, args) == True{} : Bool}
) -> {gn.pin(S.parse.take_pos.keep(keep, aa, tt), args) == True{} : Bool}:
  match keep:
    case True{}:
      hh
    case False{}:
      match aa:
        case S.Arg{+nn, _s, _l, _k, _h, _r, _d, _c}:
          gv.and_r(Laws.has_arg(args, nn), gn.pin(tt, args), hh)

# a positional binds the word, under its own name
def gn.take_pos(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  pos: List<&2, S.Arg>,
  +raw: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), ws):
  match pos:
    case Nil{}:
      gn.keep(args, binds, [], ws, hb, {==})
    case Con{ph, +tt}:
      match ph:
        case S.Arg{+name, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          gn.choice(S.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt), raw, True{}, ws,
            gv.and_l(Laws.has_arg(args, name), gn.pin(tt, args), hp), gv.ok_in(ws, tok, hh), hb,
            gn.kpos(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt, args, hp))

# entering a subcommand: its positionals are its own, and it has no bindings
def gn.enter(
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +ws: List<&2, String>
) -> gn.G(S.parse.enter(ss, args, up, path, binds), ws):
  match ss:
    case S.Sub{_n, _a, +next, _c}:
      gv.and_tt(gn.pin(S.pos_of(next), next), True{}, gn.pin_of(next), {==})

# a subcommand entered, or a missing positional
def gn.enter_or(
  miss: Maybe<&2, String>,
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), ws):
  match miss:
    case None{}:
      gn.enter(ss, args, up, path, binds, ws)
    case Some{_n}:
    gn.keep(args, binds, pos, ws, hb, hp)

# a word: a subcommand, or a positional
def gn.word_go(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
      gn.take_pos(tok, args, up, subs, path, binds, pos, raw, ws, hh, hb, hp)
    case Some{ss}:
      gn.enter_or(S.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen, ws, hb, hp)

# a word
def gn.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), ws):
  gn.word_go(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hb, hp)

# `-` alone is a word; otherwise a cluster
def gn.short_go(
  alone: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), ws):
  match alone:
    case True{}:
      gn.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hp)
    case False{}:
      gn.short(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 1n, ws, hh), hb, hp)

# a short option or a word
def gn.step_short(
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match dash:
    case True{}:
      gn.short_go(String.is_empty(String.drop(tok, 1n)), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hp)
    case False{}:
      gn.word(tok, args, up, subs, path, binds, pos, False{}, seen, ws, hh, hb, hp)

# a long option, a short one, or a word
def gn.kind_go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen), ws):
  match long:
    case True{}:
      gn.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen, ws,
        gv.in_drop(tok, 2n, ws, hh), hb, hp)
    case False{}:
      gn.step_short(dash, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hp)

# a word by its shape
def gn.skind(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.kind(tok, args, up, subs, path, binds, pos, seen), ws):
  gn.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds, pos, seen,
    ws,
    hh, hb, hp)

# `help` starts a help path
def gn.help(
  hit: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), ws):
  match hit:
    case True{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.skind(tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hp)

# `--` switches to positionals
def gn.end(
  end: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), ws):
  match end:
    case True{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen, ws, hh,
        hb, hp)

# after `--` a word is a positional
def gn.raw(
  raw: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), ws):
  match raw:
    case True{}:
      gn.take_pos(tok, args, up, subs, path, binds, pos, True{}, ws, hh, hb, hp)
    case False{}:
      gn.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hp)

# a waiting option binds the word under its own name
def gn.need(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hn: {Laws.has_arg(args, name) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match flag:
    case True{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case False{}:
      gn.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen, ws, hn, gv.ok_in(ws, tok, hh), hb, hp)

# a word of a help path
def gn.help_path(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.help_path(found, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match found:
    case None{}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case Some{ss}:
      match ss:
        case S.Sub{_n, _a, _g, _c}:
      gn.keep(args, binds, pos, ws, hb, hp)

# one word, by the walker's mode
def gn.mode(
  mode: S.Mode,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hm: {gn.min(mode, args) == True{} : Bool},
  +hb: {gn.all(binds, args, ws) == True{} : Bool},
  +hp: {gn.pin(pos, args) == True{} : Bool}
) -> gn.G(S.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen), ws):
  match mode:
    case S.Dead{_e}:
    gn.keep(args, binds, pos, ws, hb, hp)
    case S.Need{name}:
      gn.need(S.looks_flag(tok), name, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh, hm, hb, hp)
    case S.Help{}:
      gn.help_path(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, ws, hb, hp)
    case S.Free{}:
      gn.raw(raw, tok, args, up, subs, path, binds, pos, seen, ws, hh, hb, hp)

# one word within the words keeps a walker good
def gn.step(
  +tok: String,
  st: S.St,
  +ws: List<&2, String>,
  +hh: {gv.sufs(tok, ws) == True{} : Bool},
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> gn.G(S.parse.step(tok, st), ws):
  match st:
    case S.St{+mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      +hw = {gv.and_l(Bool.and(gn.min(mode, args), gn.pin(pos, args)), gn.all(binds, args, ws), hg)
        : {Bool.and(gn.min(mode, args), gn.pin(pos, args)) == True{} : Bool}}
      gn.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen, ws, hh,
        gv.and_l(gn.min(mode, args), gn.pin(pos, args), hw),
        gv.and_r(Bool.and(gn.min(mode, args), gn.pin(pos, args)), gn.all(binds, args, ws), hg),
        gv.and_r(gn.min(mode, args), gn.pin(pos, args), hw))

# a good walker, from one list of words to an equal one
def gn.tr(
  st: S.St,
  +aa: List<&2, String>,
  +bb: List<&2, String>,
  ee: {aa == bb : List<&2, String>},
  hg: {gn.good(st, bb) == True{} : Bool}
) -> {gn.good(st, aa) == True{} : Bool}:
  e2 = Equal.sym(List<&2, String>, aa, bb, ee)
  %e2 : {gn.good(st, _) == True{} : Bool}
  hg

# walking the words after `pre` keeps a walker good
def gn.walk(
  tt: List<&2, String>,
  +pre: List<&2, String>,
  +st: S.St,
  +hg: {gn.good(st, List.append(&2, String, pre, tt)) == True{} : Bool}
) -> {gn.good(S.parse.walk(tt, st), List.append(&2, String, pre, tt)) == True{} : Bool}:
  match tt:
    case Nil{}:
      hg
    case Con{+tok, +rest}:
      +ll = List.append(&2, String, pre, tok <> rest)
      +mm = List.append(&2, String, List.append(&2, String, pre, [tok]), rest)
      +ee = {M2.sc.app(pre, [tok], rest) : {mm == ll : List<&2, String>}}
      g1 = gn.step(tok, st, ll, gv.in_mid(pre, tok, rest), hg)
      gw = gn.walk(rest, List.append(&2, String, pre, [tok]), S.parse.step(tok, st),
        gn.tr(S.parse.step(tok, st), mm, ll, ee, g1))
      gn.tr(S.parse.walk(rest, S.parse.step(tok, st)), ll, mm, Equal.sym(List<&2, String>, mm, ll, ee), gw)

# a fresh walker is good
def gn.start(spec: Shake.Cli, +ws: List<&2, String>) -> {gn.good(S.parse.start(spec), ws) == True{} : Bool}:
  match spec:
    case S.Cli{_n, _a, _v, +args, _s}:
      gv.and_tt(gn.pin(S.pos_of(args), args), True{}, gn.pin_of(args), {==})

# the bindings of a view's command, named and within the words
def gn.vall(vv: Grow.View, +ws: List<&2, String>) -> Bool:
  Grow.View{aa, _u, _p, bb} = vv
  gn.all(bb, aa, ws)

# a good walker's view holds its bindings
def gn.vall_of(
  st: S.St,
  +ws: List<&2, String>,
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> {gn.vall(Grow.view(st), ws) == True{} : Bool}:
  match st:
    case S.St{+mode, +aa, _g, _s, _p, +bb, +oo, _r, _n}:
      gv.and_r(Bool.and(gn.min(mode, aa), gn.pin(oo, aa)), gn.all(bb, aa, ws), hg)

# a good walker's waiting option and positionals are its command's own,
# whatever the words
def gn.wf_of(
  st: S.St,
  +ws: List<&2, String>,
  +hg: {gn.good(st, ws) == True{} : Bool}
) -> {gn.wf(st) == True{} : Bool}:
  match st:
    case S.St{+mode, +aa, _g, _s, _p, +bb, +oo, _r, _n}:
      gv.and_l(Bool.and(gn.min(mode, aa), gn.pin(oo, aa)), gn.all(bb, aa, ws), hg)

# the two halves make a good walker
def gn.join(
  st: S.St,
  +ws: List<&2, String>,
  +hw: {gn.wf(st) == True{} : Bool},
  +ha: {gn.vall(Grow.view(st), ws) == True{} : Bool}
) -> {gn.good(st, ws) == True{} : Bool}:
  match st:
    case S.St{+mode, +aa, _g, _s, _p, +bb, +oo, _r, _n}:
      gv.and_tt(Bool.and(gn.min(mode, aa), gn.pin(oo, aa)), gn.all(bb, aa, ws), hw, ha)

# bindings named after the arguments and within the words are named and given
def gn.all_named(
  bs: List<&2, S.Bind>,
  +args: List<&2, S.Arg>,
  +ws: List<&2, String>,
  +hh: {gn.all(bs, args, ws) == True{} : Bool}
) -> {Laws.all_named(bs, ws, args) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{hd, +tt}:
      match hd:
        case S.Bind{+nn, +vv}:
          +hn = {gv.and_l(gn.nok(args, ws, S.Bind{nn, vv}), gn.all(tt, args, ws), hh)
            : {Bool.and(Laws.has_arg(args, nn), gv.ok(ws, vv)) == True{} : Bool}}
          gv.and_tt(Laws.named_given(ws, args, S.Bind{nn, vv}), Laws.all_named(tt, ws, args),
            gv.and_tt(Laws.has_arg(args, nn), D1.given(ws, args, S.Bind{nn, vv}),
              gv.and_l(Laws.has_arg(args, nn), gv.ok(ws, vv), hn),
              gv.or3(String.eq(vv, "true"), D1.piece(ws, vv), D1.is_default(args, nn, vv),
                gv.and_r(Laws.has_arg(args, nn), gv.ok(ws, vv), hn))),
            gn.all_named(tt, args, ws, gv.and_r(gn.nok(args, ws, S.Bind{nn, vv}), gn.all(tt, args, ws), hh)))

# whether an argument's default, when it has one, is a default of `args`
# under a name one of them has
def gn.dcase(dd: Maybe<&2, String>, +an: String, +args: List<&2, S.Arg>) -> Bool:
  match dd:
    case None{}:
      True{}
    case Some{dv}:
      Bool.and(Laws.has_arg(args, an), D1.is_default(args, an, dv))

# whether every default of some arguments is a default of `args`
def gn.dsub(tt: List<&2, S.Arg>, +args: List<&2, S.Arg>) -> Bool:
  match tt:
    case Nil{}:
      True{}
    case Con{aa, rest}:
      S.Arg{+an, _s, _l, _k, _h, _r, S.Fallback{_e, dd}, _c} = aa
      Bool.and(gn.dcase(dd, an, args), gn.dsub(rest, args))

# a default of some arguments is a default of more
def gn.dcase_mono(
  dd: Maybe<&2, String>,
  +an: String,
  aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {gn.dcase(dd, an, tt) == True{} : Bool}
) -> {gn.dcase(dd, an, aa <> tt) == True{} : Bool}:
  match dd:
    case None{}:
      {==}
    case Some{+dv}:
      match aa:
        case S.Arg{+bn, +bs, +bl, +bk, +bh, +br, S.Fallback{+ev, +bd}, +bc}:
          gv.and_tt(Laws.has_arg(S.Arg{bn, bs, bl, bk, bh, br, S.Fallback{ev, bd}, bc} <> tt, an),
            D1.is_default(S.Arg{bn, bs, bl, bk, bh, br, S.Fallback{ev, bd}, bc} <> tt, an, dv),
            gn.or_rt(String.eq(bn, an), Laws.has_arg(tt, an),
              gv.and_l(Laws.has_arg(tt, an), D1.is_default(tt, an, dv), hh)),
            gn.or_rt(Bool.and(String.eq(bn, an), D1.default_is(bd, dv)), D1.is_default(tt, an, dv),
              gv.and_r(Laws.has_arg(tt, an), D1.is_default(tt, an, dv), hh)))

# the defaults of some arguments are defaults of more
def gn.dsub_mono(
  xs: List<&2, S.Arg>,
  +aa: S.Arg,
  +tt: List<&2, S.Arg>,
  +hh: {gn.dsub(xs, tt) == True{} : Bool}
) -> {gn.dsub(xs, aa <> tt) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{xx, +xt}:
      match xx:
        case S.Arg{+xn, _s, _l, _k, _h, _r, S.Fallback{_e, +xd}, _c}:
          gv.and_tt(gn.dcase(xd, xn, aa <> tt), gn.dsub(xt, aa <> tt),
            gn.dcase_mono(xd, xn, aa, tt, gv.and_l(gn.dcase(xd, xn, tt), gn.dsub(xt, tt), hh)),
            gn.dsub_mono(xt, aa, tt, gv.and_r(gn.dcase(xd, xn, tt), gn.dsub(xt, tt), hh)))

# an argument's own default is a default of a list it heads
def gn.dcase_self(
  +ev: Maybe<&2, String>,
  dd: Maybe<&2, String>,
  +an: String,
  +sh: Maybe<&2, String>,
  +lo: Maybe<&2, String>,
  +kind: S.ArgKind,
  +hl: String,
  +req: Bool,
  +cs: List<&2, String>,
  +tt: List<&2, S.Arg>
) -> {gn.dcase(dd, an, S.Arg{an, sh, lo, kind, hl, req, S.Fallback{ev, dd}, cs} <> tt) == True{} : Bool}:
  match dd:
    case None{}:
      {==}
    case Some{+dv}:
      e1 = Equal.sym(Bool, String.eq(an, an), True{}, Eq.string_eq_self(an))
      e2 = Equal.sym(Bool, String.eq(dv, dv), True{}, Eq.string_eq_self(dv))
      %e1 : {Bool.and(Bool.or(_, Laws.has_arg(tt, an)),
          Bool.or(Bool.and(_, String.eq(dv, dv)), D1.is_default(tt, an, dv)))
        == True{} : Bool}
      %e2 : {Bool.and(Bool.or(True{}, Laws.has_arg(tt, an)), Bool.or(Bool.and(True{}, _), D1.is_default(tt, an, dv)))
        == True{} : Bool}
      {==}

# every argument's default is a default of the list
def gn.dsub_self(args: List<&2, S.Arg>) -> {gn.dsub(args, args) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{aa, +tt}:
      match aa:
        case S.Arg{+an, +sh, +lo, +kind, +hl, +req, S.Fallback{+ev, +dd}, +cs}:
          gv.and_tt(gn.dcase(dd, an, S.Arg{an, sh, lo, kind, hl, req, S.Fallback{ev, dd}, cs} <> tt),
            gn.dsub(tt, S.Arg{an, sh, lo, kind, hl, req, S.Fallback{ev, dd}, cs} <> tt),
            gn.dcase_self(ev, dd, an, sh, lo, kind, hl, req, cs, tt),
            gn.dsub_mono(tt, S.Arg{an, sh, lo, kind, hl, req, S.Fallback{ev, dd}, cs}, tt, gn.dsub_self(tt)))

# a default goes in front when its name is unbound, named and given
def gn.fone(
  skip: Bool,
  +nn: String,
  +vv: String,
  +rr: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hr: {Laws.all_named(rr, ws, args) == True{} : Bool},
  +hd: {Laws.named_given(ws, args, S.Bind{nn, vv}) == True{} : Bool}
) -> {Laws.all_named(S.fill.one(skip, nn, vv, rr), ws, args) == True{} : Bool}:
  match skip:
    case True{}:
      hr
    case False{}:
      gv.and_tt(Laws.named_given(ws, args, S.Bind{nn, vv}), Laws.all_named(rr, ws, args), hd, hr)

# `x`, or `y` or something true, is true
def gn.or_rr(
  +xx: Bool,
  +yy: Bool,
  zz: Bool,
  +hh: {zz == True{} : Bool}
) -> {Bool.or(xx, Bool.or(yy, zz)) == True{} : Bool}:
  ee = Equal.sym(Bool, zz, True{}, hh)
  e2 = Equal.sym(Bool, Bool.or(yy, True{}), True{}, gv.or_t(yy))
  %ee : {Bool.or(xx, Bool.or(yy, _)) == True{} : Bool}
  %e2 : {Bool.or(xx, _) == True{} : Bool}
  gv.or_t(xx)

# one argument's default, filled when unbound
def gn.fill_arg(
  dd: Maybe<&2, String>,
  +an: String,
  +rr: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hr: {Laws.all_named(rr, ws, args) == True{} : Bool},
  +hd: {gn.dcase(dd, an, args) == True{} : Bool}
) -> {Laws.all_named(S.fill.arg.go(dd, an, rr), ws, args) == True{} : Bool}:
  match dd:
    case None{}:
      hr
    case Some{+dv}:
      gn.fone(S.bound(rr, an), an, dv, rr, ws, args, hr,
        gv.and_tt(Laws.has_arg(args, an), D1.given(ws, args, S.Bind{an, dv}),
          gv.and_l(Laws.has_arg(args, an), D1.is_default(args, an, dv), hd),
          gn.or_rr(String.eq(dv, "true"), D1.piece(ws, dv), D1.is_default(args, an, dv),
            gv.and_r(Laws.has_arg(args, an), D1.is_default(args, an, dv), hd))))

# the defaults filled in are named and given
def gn.fill(
  tt: List<&2, S.Arg>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +hb: {Laws.all_named(bs, ws, args) == True{} : Bool},
  +hs: {gn.dsub(tt, args) == True{} : Bool}
) -> {Laws.all_named(S.fill.args(tt, bs), ws, args) == True{} : Bool}:
  match tt:
    case Nil{}:
      hb
    case Con{aa, +rest}:
      match aa:
        case S.Arg{+an, _s, _l, _k, _h, _r, S.Fallback{_e, +dd}, _c}:
          gn.fill_arg(dd, an, S.fill.args(rest, bs), ws, args,
            gn.fill(rest, args, bs, ws, hb, gv.and_r(gn.dcase(dd, an, args), gn.dsub(rest, args), hs)),
            gv.and_l(gn.dcase(dd, an, args), gn.dsub(rest, args), hs))

# reversed bindings are named and given when they are
def gn.rev_named(
  xs: List<&2, S.Bind>,
  +acc: List<&2, S.Bind>,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +hx: {Laws.all_named(xs, ws, args) == True{} : Bool},
  +ha: {Laws.all_named(acc, ws, args) == True{} : Bool}
) -> {Laws.all_named(List.reverse.go(&2, S.Bind, xs, acc), ws, args) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+hd, +tt}:
      gn.rev_named(tt, hd <> acc, ws, args,
        gv.and_r(Laws.named_given(ws, args, hd), Laws.all_named(tt, ws, args), hx),
        gv.and_tt(Laws.named_given(ws, args, hd), Laws.all_named(acc, ws, args),
          gv.and_l(Laws.named_given(ws, args, hd), Laws.all_named(tt, ws, args), hx), ha))

# the words `ws` leave the walker at the command with these arguments, above
# these levels, at this path, with these bindings
def gn.At(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>
) -> Type:
  {Grow.view(S.parse.walk(ws, S.parse.start(spec))) == Grow.View{args, up, path, bs} : Grow.View}

# the bindings a command made while it was current are named and within its
# words
def gn.here(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +mid: List<&2, String>,
  +args: List<&2, S.Arg>,
  +bs: List<&2, S.Bind>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  h_pre: gn.At(spec, pre, args, up, path, []),
  h_mid: gn.At(spec, List.append(&2, String, pre, mid), args, up, path, bs)
) -> {gn.all(bs, args, mid) == True{} : Bool}:
  +s1 = S.parse.walk(pre, S.parse.start(spec))
  +s2 = S.parse.walk(mid, s1)
  +v0 = {Grow.View{args, up, path, []} : Grow.View}
  +v2 = {Grow.View{args, up, path, bs} : Grow.View}
  hw = gn.wf_of(s1, pre, gn.walk(pre, [], S.parse.start(spec), gn.start(spec, pre)))
  ha = Equal.trans(Bool, gn.vall(Grow.view(s1), mid), gn.vall(v0, mid), True{},
    Equal.cong(Grow.View, Bool, vv => gn.vall(vv, mid), Grow.view(s1), v0, h_pre), {==})
  +wm = S.parse.walk(List.append(&2, String, pre, mid), S.parse.start(spec))
  e2 = Equal.trans(Grow.View, Grow.view(s2), Grow.view(wm), v2,
    Equal.cong(S.St, Grow.View, st => Grow.view(st), s2, wm,
      Equal.sym(S.St, wm, s2, L1.walk_append(pre, mid, S.parse.start(spec)))),
    h_mid)
  Equal.trans(Bool, gn.vall(v2, mid), gn.vall(Grow.view(s2), mid), True{},
    Equal.cong(Grow.View, Bool, vv => gn.vall(vv, mid), v2, Grow.view(s2), Equal.sym(Grow.View, Grow.view(s2), v2, e2)),
    gn.vall_of(s2, mid, gn.walk(mid, [], s1, gn.join(s1, mid, hw, ha))))

def Laws.values_here(spec, pre, mid, post, found, qs, args, bs, up, path, ms, h_done, h_pre, h_mid, h_fr, h_len):
  +ws = List.append(&2, String, pre, List.append(&2, String, mid, post))
  +f0 = {S.Level{args, S.fill.args(args, bs)} : S.Level}
  +rq = List.reverse(&2, S.Level, S.fill.levels(qs))
  ea = Equal.sym(Maybe<&2, S.Matched>, S.at(found, path), Some{S.matched.build(f0 <> rq, ms)},
    M1.fin.at(spec, ws, found, qs, args, bs, up, path, ms, h_done, h_fr, h_len))
  eo = Equal.sym(List<&2, S.Bind>, S.own(S.matched.build(f0 <> rq, ms)),
    List.reverse(&2, S.Bind, S.fill.args(args, bs)), Grow.gw.own_build(f0, rq, ms))
  %ea : {Laws.named_at.go(_, mid, args) == Some{True{}} : Maybe<&2, Bool>}
  %eo : {Some{Laws.all_named(_, mid, args)} == Some{True{}} : Maybe<&2, Bool>}
  Equal.cong(Bool, Maybe<&2, Bool>, bb => Some{bb},
    Laws.all_named(List.reverse(&2, S.Bind, S.fill.args(args, bs)), mid, args), True{},
    gn.rev_named(S.fill.args(args, bs), [], mid, args,
      gn.fill(args, args, bs, mid,
        gn.all_named(bs, args, mid, gn.here(spec, pre, mid, args, bs, up, path, h_pre, h_mid)),
        gn.dsub_self(args)),
      {==}))

# ---- laws/BindingsComeFromWords.bend: a word binds at most one value

# a walker's bindings count at most `kk` values
def nd.T(st: S.St, +kk: Nat) -> Type:
  {Laws.nat_le(Laws.valued(Laws.binds_of(st)), kk) == True{} : Bool}

# a count is at most itself
def nd.le_refl(nn: Nat) -> {Laws.nat_le(nn, nn) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      nd.le_refl(pp)

# a count is at most one more
def nd.le_s(nn: Nat) -> {Laws.nat_le(nn, 1n+nn) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      nd.le_s(pp)

# at most is transitive
def nd.le_trans(
  aa: Nat,
  bb: Nat,
  cc: Nat,
  h1: {Laws.nat_le(aa, bb) == True{} : Bool},
  h2: {Laws.nat_le(bb, cc) == True{} : Bool}
) -> {Laws.nat_le(aa, cc) == True{} : Bool}:
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      match bb:
        case 0n:
          Empty.absurd({Laws.nat_le(1n+pp, cc) == True{} : Bool}, Walk.wk.false_true(h1))
        case 1n+qq:
          match cc:
            case 0n:
              Empty.absurd({False{} == True{} : Bool}, Walk.wk.false_true(h2))
            case 1n+rr:
              nd.le_trans(pp, qq, rr, h1, h2)

# a binding in front counts at most one more
def nd.put_le(flag: Bool, +nn: Nat) -> {Laws.nat_le(Laws.valued.at(flag, nn), 1n+nn) == True{} : Bool}:
  match flag:
    case True{}:
      nd.le_s(nn)
    case False{}:
      nd.le_refl(1n+nn)

# the once-check keeps the walker's bindings
def nd.once_keep(
  again: Bool,
  st: S.St,
  +name: String,
  +path: List<&2, String>
) -> {Laws.binds_of(S.parse.once(again, st, name, path)) == Laws.binds_of(st) : List<&2, S.Bind>}:
  match again:
    case True{}:
      match st:
        case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
          {==}
    case False{}:
      {==}

# the once-check keeps a count
def nd.once(
  again: Bool,
  +st: S.St,
  +name: String,
  +path: List<&2, String>,
  +kk: Nat,
  hh: {Laws.nat_le(Laws.valued(Laws.binds_of(st)), kk) == True{} : Bool}
) -> nd.T(S.parse.once(again, st, name, path), kk):
  ee = Equal.sym(List<&2, S.Bind>, Laws.binds_of(S.parse.once(again, st, name, path)), Laws.binds_of(st),
    nd.once_keep(again, st, name, path))
  %ee : {Laws.nat_le(Laws.valued(_), kk) == True{} : Bool}
  hh

# a binding
def nd.put(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  nd.put_le(String.eq(val, "true"), Laws.valued(binds))

# a value bound when allowed
def nd.choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match ok:
    case True{}:
      nd.put(name, val, args, up, subs, path, binds, pos, raw, seen)
    case False{}:
    nd.le_s(Laws.valued(binds))

# an option's value
def nd.opt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  nd.choice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos, raw,
    seen)

# a flag
def nd.flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match val:
    case None{}:
      nd.put(name, "true", args, up, subs, path, binds, pos, raw, seen)
    case Some{_v}:
    nd.le_s(Laws.valued(binds))

# an option
def nd.opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match val:
    case None{}:
    nd.le_s(Laws.valued(binds))
    case Some{vv}:
      nd.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen)

# a found argument, by its kind
def nd.akind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw,
  seen), 1n+Laws.valued(binds)):
  match kk:
    case S.Flag{}:
      nd.once(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, 1n+Laws.valued(binds), nd.flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen))
    case S.Opt{}:
      nd.once(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, 1n+Laws.valued(binds), nd.opt(val, name, args, up, subs, path, binds, pos, raw, seen))
    case S.Many{}:
      nd.opt(val, name, args, up, subs, path, binds, pos, raw, seen)
    case S.Pos{}:
    nd.le_s(Laws.valued(binds))
    case S.Rest{}:
    nd.le_s(Laws.valued(binds))

# a found argument, or an unknown flag
def nd.arg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match found:
    case None{}:
    nd.le_s(Laws.valued(binds))
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          nd.akind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen)

# an unknown long option: a request for help, or an unknown flag
def nd.lhelp(
  hit: Bool,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_long.help(hit, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match hit:
    case True{}:
      nd.le_s(Laws.valued(binds))
    case False{}:
      nd.le_s(Laws.valued(binds))

# a long option the current command spells, or an unknown one
def nd.found(
  found: Maybe<&2, S.Arg>,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_long.found(found, name, val, orig, args, up, subs, path, binds, pos, raw, seen),
  1n+Laws.valued(binds)):
  match found:
    case None{}:
      nd.lhelp(S.long_help(name, val, seen), orig, args, up, subs, path, binds, pos, raw, seen)
    case Some{aa}:
      nd.arg(Some{aa}, val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option with a name
def nd.named(
  empty: Bool,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw,
  seen), 1n+Laws.valued(binds)):
  match empty:
    case True{}:
    nd.le_s(Laws.valued(binds))
    case False{}:
      nd.found(S.by_long(args, name), name, val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option after the `=` cut
def nd.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match nv:
    case (+name, +val):
      nd.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen)

# a long option
def nd.long(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  nd.cut(S.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen)

# the bound on a cluster so far: the count it started with while no letter
# has ended it, one more once one has
def nd.inv(st: S.St, +n0: Nat, done: Bool) -> Bool:
  match done:
    case True{}:
      Laws.nat_le(Laws.valued(Laws.binds_of(st)), 1n+n0)
    case False{}:
      Laws.nat_le(Laws.valued(Laws.binds_of(st)), n0)

# a walker within the count it started with is within the bound, ended or not
def nd.inv_any(
  done: Bool,
  +st: S.St,
  +n0: Nat,
  +hh: {Laws.nat_le(Laws.valued(Laws.binds_of(st)), n0) == True{} : Bool}
) -> {nd.inv(st, n0, done) == True{} : Bool}:
  match done:
    case True{}:
      nd.le_trans(Laws.valued(Laws.binds_of(st)), n0, 1n+n0, hh, nd.le_s(n0))
    case False{}:
      hh

# one more than a count within the start, lifted
def nd.lift(
  +st: S.St,
  +bs: List<&2, S.Bind>,
  +n0: Nat,
  ht: {Laws.nat_le(Laws.valued(Laws.binds_of(st)), 1n+Laws.valued(bs)) == True{} : Bool},
  hh: {Laws.nat_le(Laws.valued(bs), n0) == True{} : Bool}
) -> {nd.inv(st, n0, True{}) == True{} : Bool}:
  nd.le_trans(Laws.valued(Laws.binds_of(st)), 1n+Laws.valued(bs), 1n+n0, ht, hh)

# a flag letter: `true` goes on, or `=` ends the cluster refused
def nd.lflag(
  eq: Bool,
  +name: String,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +n0: Nat,
  +hh: {Laws.nat_le(Laws.valued(binds), n0) == True{} : Bool}
) -> {nd.inv(S.parse.once(S.bound(binds, name), S.parse.take_flag(S.cluster.val.flag(eq, rest), name, orig, args, up,
    subs, path, binds, pos, raw, seen), name, path), n0, eq) == True{} : Bool}:
  match eq:
    case True{}:
      +st = S.parse.take_flag(Some{rest}, name, orig, args, up, subs, path, binds, pos, raw, seen)
      ee = Equal.sym(List<&2, S.Bind>, Laws.binds_of(S.parse.once(S.bound(binds, name), st, name, path)),
        Laws.binds_of(st), nd.once_keep(S.bound(binds, name), st, name, path))
      %ee : {Laws.nat_le(Laws.valued(_), 1n+n0) == True{} : Bool}
      nd.le_trans(Laws.valued(binds), n0, 1n+n0, hh, nd.le_s(n0))
    case False{}:
      +st = S.parse.take_flag(None{}, name, orig, args, up, subs, path, binds, pos, raw, seen)
      ee = Equal.sym(List<&2, S.Bind>, Laws.binds_of(S.parse.once(S.bound(binds, name), st, name, path)),
        Laws.binds_of(st), nd.once_keep(S.bound(binds, name), st, name, path))
      %ee : {Laws.nat_le(Laws.valued(_), n0) == True{} : Bool}
      hh

# a letter's effect, and whether it ends the cluster
def nd.lpair(
  found: Maybe<&2, S.Arg>,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +n0: Nat,
  +hh: {Laws.nat_le(Laws.valued(binds), n0) == True{} : Bool}
) -> {nd.inv(S.parse.take_arg(found, S.cluster.val(found, rest), orig, args, up, subs, path, binds, pos, raw, seen), n0,
    S.cluster.ends(found, rest)) == True{} : Bool}:
  match found:
    case None{}:
      nd.le_trans(Laws.valued(binds), n0, 1n+n0, hh, nd.le_s(n0))
    case Some{aa}:
      match aa:
        case S.Arg{+name, +sh, +lo, kind, +hl, +req, +dd, +cs}:
          match kind:
            case S.Flag{}:
              nd.lflag(String.starts_with(rest, "="), name, rest, orig, args, up, subs, path, binds, pos, raw, seen, n0,
                hh)
            case S.Opt{}:
              +vv = S.short_of.val(String.starts_with(rest, "="), rest)
              nd.lift(S.parse.once(S.bound(binds, name), S.parse.take_opt(vv, name, args, up, subs, path, binds, pos,
                raw,
                seen), name, path), binds, n0,
                nd.once(S.bound(binds, name), S.parse.take_opt(vv, name, args, up, subs, path, binds, pos, raw, seen),
                  name, path, 1n+Laws.valued(binds), nd.opt(vv, name, args, up, subs, path, binds, pos, raw, seen)), hh)
            case S.Many{}:
              +vv = S.short_of.val(String.starts_with(rest, "="), rest)
              nd.lift(S.parse.take_opt(vv, name, args, up, subs, path, binds, pos, raw, seen), binds, n0,
                nd.opt(vv, name, args, up, subs, path, binds, pos, raw, seen), hh)
            case S.Pos{}:
              nd.le_trans(Laws.valued(binds), n0, 1n+n0, hh, nd.le_s(n0))
            case S.Rest{}:
              nd.le_trans(Laws.valued(binds), n0, 1n+n0, hh, nd.le_s(n0))

# a walker within the bound is within one more than the start
def nd.inv_out(
  done: Bool,
  +st: S.St,
  +n0: Nat,
  +hh: {nd.inv(st, n0, done) == True{} : Bool}
) -> nd.T(st, 1n+n0):
  match done:
    case True{}:
      hh
    case False{}:
      nd.le_trans(Laws.valued(Laws.binds_of(st)), n0, 1n+n0, hh, nd.le_s(n0))

# one letter, by the walker's mode
def nd.cmode(
  mode: S.Mode,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +n0: Nat,
  +hh: {Laws.nat_le(Laws.valued(binds), n0) == True{} : Bool}
) -> {nd.inv(S.cluster.apply.mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen), n0,
    S.cluster.ends(S.by_short(args, SCon{cc, SNil{}}), rest)) == True{} : Bool}:
  match mode:
    case S.Dead{+ee}:
      nd.inv_any(S.cluster.ends(S.by_short(args, SCon{cc, SNil{}}), rest),
        S.St{S.Dead{ee}, args, up, subs, path, binds, pos, raw, seen}, n0, hh)
    case S.Free{}:
      nd.lpair(S.by_short(args, SCon{cc, SNil{}}), rest, orig, args, up, subs, path, binds, pos, raw, seen, n0, hh)
    case S.Need{_n}:
      nd.lpair(S.by_short(args, SCon{cc, SNil{}}), rest, orig, args, up, subs, path, binds, pos, raw, seen, n0, hh)
    case S.Help{}:
      nd.lpair(S.by_short(args, SCon{cc, SNil{}}), rest, orig, args, up, subs, path, binds, pos, raw, seen, n0, hh)

# one letter against a walker within the start
def nd.capply(
  st: S.St,
  +cc: Char,
  +rest: String,
  +orig: String,
  +n0: Nat,
  +hh: {Laws.nat_le(Laws.valued(Laws.binds_of(st)), n0) == True{} : Bool}
) -> {nd.inv(S.cluster.apply(st, cc, rest, orig), n0, S.cluster.done(False{}, cc, rest, st)) == True{} : Bool}:
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      nd.cmode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen, n0, hh)

# a letter, and whether the cluster goes on
def nd.letter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  +st: S.St,
  +n0: Nat,
  +hh: {nd.inv(st, n0, done) == True{} : Bool}
) -> {nd.inv(S.cluster.letter(done, cc, rest, orig, st), n0, S.cluster.done(done, cc, rest, st)) == True{} : Bool}:
  match done:
    case True{}:
      hh
    case False{}:
      nd.capply(st, cc, rest, orig, n0, hh)

# a whole cluster adds at most one value to what it started with
def nd.cluster(
  body: String,
  +orig: String,
  +st: S.St,
  +done: Bool,
  +n0: Nat,
  +hh: {nd.inv(st, n0, done) == True{} : Bool}
) -> nd.T(S.cluster(body, orig, st, done), 1n+n0):
  match body:
    case SNil{}:
      nd.inv_out(done, st, n0, hh)
    case SCon{+cc, +rest}:
      nd.cluster(rest, orig, S.cluster.letter(done, cc, rest, orig, st), S.cluster.done(done, cc, rest, st), n0,
        nd.letter(done, cc, rest, orig, st, n0, hh))

# a short option: a request for help, or a cluster
def nd.sgo(
  hit: Bool,
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_short.go(hit, body, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match hit:
    case True{}:
      nd.le_s(Laws.valued(binds))
    case False{}:
      nd.cluster(body, orig, S.St{S.Free{}, args, up, subs, path, binds, pos, raw, seen}, False{}, Laws.valued(binds),
        nd.le_refl(Laws.valued(binds)))

# a short option
def nd.short(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.take_short(body, orig, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  nd.sgo(S.short_help(body, args, seen), body, orig, args, up, subs, path, binds, pos, raw, seen)

# a positional
def nd.take_pos(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  pos: List<&2, S.Arg>,
  +raw: Bool
) -> nd.T(S.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), 1n+Laws.valued(binds)):
  match pos:
    case Nil{}:
    nd.le_s(Laws.valued(binds))
    case Con{ph, +tt}:
      match ph:
        case S.Arg{+name, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          nd.choice(S.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt), raw, True{})

# entering a subcommand starts with no bindings
def nd.enter(
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>
) -> nd.T(S.parse.enter(ss, args, up, path, binds), 1n+Laws.valued(binds)):
  match ss:
    case S.Sub{_n, _a, _g, _c}:
      {==}

# a subcommand entered, or a missing positional
def nd.enter_or(
  miss: Maybe<&2, String>,
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match miss:
    case None{}:
      nd.enter(ss, args, up, path, binds)
    case Some{_n}:
    nd.le_s(Laws.valued(binds))

# a word
def nd.word_go(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match found:
    case None{}:
      nd.take_pos(tok, args, up, subs, path, binds, pos, raw)
    case Some{ss}:
      nd.enter_or(S.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen)

# a word
def nd.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  nd.word_go(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen)

# `-` alone, or a cluster
def nd.short_go(
  alone: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match alone:
    case True{}:
      nd.word(tok, args, up, subs, path, binds, pos, False{}, seen)
    case False{}:
      nd.short(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, False{}, seen)

# a short option or a word
def nd.step_short(
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match dash:
    case True{}:
      nd.short_go(String.is_empty(String.drop(tok, 1n)), tok, args, up, subs, path, binds, pos, seen)
    case False{}:
      nd.word(tok, args, up, subs, path, binds, pos, False{}, seen)

# a long option, a short one, or a word
def nd.kind_go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match long:
    case True{}:
      nd.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen)
    case False{}:
      nd.step_short(dash, tok, args, up, subs, path, binds, pos, seen)

# a word by its shape
def nd.skind(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.kind(tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  nd.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds, pos, seen)

# `help`
def nd.help(
  hit: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match hit:
    case True{}:
    nd.le_s(Laws.valued(binds))
    case False{}:
      nd.skind(tok, args, up, subs, path, binds, pos, seen)

# `--`
def nd.end(
  end: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match end:
    case True{}:
    nd.le_s(Laws.valued(binds))
    case False{}:
      nd.help(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen)

# after `--`
def nd.raw(
  raw: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool
) -> nd.T(S.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), 1n+Laws.valued(binds)):
  match raw:
    case True{}:
      nd.take_pos(tok, args, up, subs, path, binds, pos, True{})
    case False{}:
      nd.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen)

# a waiting option
def nd.need(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match flag:
    case True{}:
    nd.le_s(Laws.valued(binds))
    case False{}:
      nd.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen)

# a word of a help path
def nd.help_path(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.step.help_path(found, tok, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match found:
    case None{}:
    nd.le_s(Laws.valued(binds))
    case Some{ss}:
      match ss:
        case S.Sub{_n, _a, _g, _c}:
      nd.le_s(Laws.valued(binds))

# one word, by the walker's mode
def nd.mode(
  mode: S.Mode,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> nd.T(S.parse.step.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen), 1n+Laws.valued(binds)):
  match mode:
    case S.Dead{_e}:
    nd.le_s(Laws.valued(binds))
    case S.Need{name}:
      nd.need(S.looks_flag(tok), name, tok, args, up, subs, path, binds, pos, raw, seen)
    case S.Help{}:
      nd.help_path(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen)
    case S.Free{}:
      nd.raw(raw, tok, args, up, subs, path, binds, pos, seen)

def Laws.one_value_per_word(tok, st):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      nd.mode(mode, tok, args, up, subs, path, binds, pos, raw, seen)

# ---- laws/BindingsComeFromWords.bend: no word is ignored

# whether a mode has failed, waits for a value, reads a help path
def nu.dead_m(mode: S.Mode) -> Bool:
  match mode:
    case S.Dead{_e}:
      True{}
    case S.Free{}:
      False{}
    case S.Need{_n}:
      False{}
    case S.Help{}:
      False{}

def nu.need_m(mode: S.Mode) -> Bool:
  match mode:
    case S.Need{_n}:
      True{}
    case S.Free{}:
      False{}
    case S.Dead{_e}:
      False{}
    case S.Help{}:
      False{}

def nu.help_m(mode: S.Mode) -> Bool:
  match mode:
    case S.Help{}:
      True{}
    case S.Free{}:
      False{}
    case S.Need{_n}:
      False{}
    case S.Dead{_e}:
      False{}

# a walker's mode facts, its raw switch, its binding and level counts
def nu.dead(st: S.St) -> Bool:
  S.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  nu.dead_m(mode)

def nu.need(st: S.St) -> Bool:
  S.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  nu.need_m(mode)

def nu.help(st: S.St) -> Bool:
  S.St{mode, _a, _g, _s, _p, _b, _o, _r, _n} = st
  nu.help_m(mode)

def nu.raw(st: S.St) -> Bool:
  S.St{_m, _a, _g, _s, _p, _b, _o, raw, _n} = st
  raw

def nu.blen(st: S.St) -> Nat:
  S.St{_m, _a, _g, _s, _p, binds, _o, _r, _n} = st
  List.length(&2, S.Bind, binds)

def nu.ulen(st: S.St) -> Nat:
  S.St{_m, _a, up, _s, _p, _b, _o, _r, _n} = st
  List.length(&2, S.Level, up)

# a walker that is not the other one
def nu.N(res: S.St, orig: S.St) -> Type:
  {res == orig : S.St} -> Empty

# one fact that tells two walkers apart
def nu.apart(
  +res: S.St,
  +orig: S.St,
  ff: S.St -> Bool,
  hr: {ff(res) == True{} : Bool},
  ho: {ff(orig) == False{} : Bool}
) -> nu.N(res, orig):
  ee => Walk.wk.true_false(Equal.trans(Bool, True{}, ff(res), False{}, Equal.sym(Bool, ff(res), True{}, hr),
    Equal.trans(Bool, ff(res), ff(orig), False{}, Equal.cong(S.St, Bool, ff, res, orig, ee), ho)))

# zero is not one more than a count
def nu.z_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# the count before this one
def nu.pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# no count is one more than itself
def nu.succ_ne(nn: Nat, ee: {1n+nn == nn : Nat}) -> Empty:
  match nn:
    case 0n:
      e2 = Equal.sym(Nat, 1n, 0n, ee)
      %e2 : nu.z_ty(_)
      Unit{}
    case 1n+pp:
      nu.succ_ne(pp, Equal.cong(Nat, Nat, xx => nu.pred(xx), 1n+(1n+pp), 1n+pp, ee))

# more bindings tell two walkers apart
def nu.more(
  +res: S.St,
  +orig: S.St,
  +nn: Nat,
  hr: {nu.blen(res) == 1n+nn : Nat},
  ho: {nu.blen(orig) == nn : Nat}
) -> nu.N(res, orig):
  ee => nu.succ_ne(nn, Equal.trans(Nat, 1n+nn, nu.blen(res), nn, Equal.sym(Nat, nu.blen(res), 1n+nn, hr),
    Equal.trans(Nat, nu.blen(res), nu.blen(orig), nn, Equal.cong(S.St, Nat, ss => nu.blen(ss), res, orig, ee), ho)))

# more levels tell two walkers apart
def nu.deeper(
  +res: S.St,
  +orig: S.St,
  +nn: Nat,
  hr: {nu.ulen(res) == 1n+nn : Nat},
  ho: {nu.ulen(orig) == nn : Nat}
) -> nu.N(res, orig):
  ee => nu.succ_ne(nn, Equal.trans(Nat, 1n+nn, nu.ulen(res), nn, Equal.sym(Nat, nu.ulen(res), 1n+nn, hr),
    Equal.trans(Nat, nu.ulen(res), nu.ulen(orig), nn, Equal.cong(S.St, Nat, ss => nu.ulen(ss), res, orig, ee), ho)))

# a binding tells the walker apart
def nu.put(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode
) -> nu.N(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path, binds,
  pos, raw, seen}):
  nu.more(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path, binds,
    pos, raw, seen},
    List.length(&2, S.Bind, binds), {==}, {==})

# a value bound or refused
def nu.choice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
  path, binds, pos, raw, seen}):
  match ok:
    case True{}:
      nu.put(name, val, args, up, subs, path, binds, pos, raw, seen, m0)
    case False{}:
      nu.apart(S.parse.take_choice(False{}, name, val, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args,
        up, subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)

# an option's value
def nu.opt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  nu.choice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos, raw,
    seen,
    m0, hd)

# a flag
def nu.flag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
  path, binds, pos, raw, seen}):
  match val:
    case None{}:
      nu.put(name, "true", args, up, subs, path, binds, pos, raw, seen, m0)
    case Some{+vv}:
      nu.apart(S.parse.take_flag(Some{vv}, name, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args,
        up, subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)

# an option
def nu.opt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  match val:
    case None{}:
      nu.apart(S.parse.take_opt(None{}, name, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
        path, binds, pos, raw, seen},
        ss => nu.need(ss), {==}, hn)
    case Some{vv}:
      nu.opt_val(name, vv, args, up, subs, path, binds, pos, raw, seen, m0, hd)

# a repeat fails
def nu.once_dead(
  st: S.St,
  +name: String,
  +path0: List<&2, String>
) -> {nu.dead(S.parse.once(True{}, st, name, path0)) == True{} : Bool}:
  match st:
    case S.St{_m, _a, _g, _s, _p, _b, _o, _r, _n}:
      {==}

# the once-check: a repeat fails, else the walker it was given
def nu.once(
  again: Bool,
  +st: S.St,
  +name: String,
  +path0: List<&2, String>,
  +orig: S.St,
  +hdo: {nu.dead(orig) == False{} : Bool},
  hh: nu.N(st, orig)
) -> nu.N(S.parse.once(again, st, name, path0), orig):
  match again:
    case True{}:
      nu.apart(S.parse.once(True{}, st, name, path0), orig, ss => nu.dead(ss), nu.once_dead(st, name, path0), hdo)
    case False{}:
      hh

# a found argument, by its kind
def nu.akind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up,
  subs, path, binds, pos, raw, seen}):
  match kk:
    case S.Flag{}:
      nu.once(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, S.St{m0, args, up, subs, path, binds, pos, raw, seen}, hd, nu.flag(val, name, orig, args, up,
          subs, path, binds, pos, raw, seen, m0, hd))
    case S.Opt{}:
      nu.once(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, S.St{m0, args, up, subs, path, binds, pos, raw, seen}, hd, nu.opt(val, name, args, up, subs, path,
          binds, pos, raw, seen, m0, hd, hn))
    case S.Many{}:
      nu.opt(val, name, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn)
    case S.Pos{}:
      nu.apart(S.parse.take_arg.kind(S.Pos{}, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0,
        args, up, subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)
    case S.Rest{}:
      nu.apart(S.parse.take_arg.kind(S.Rest{}, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0,
        args, up, subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)

# a found argument, or an unknown flag
def nu.arg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
  path, binds, pos, raw, seen}):
  match found:
    case None{}:
      nu.apart(S.parse.take_arg(None{}, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up,
        subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          nu.akind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn)

# an unknown long option: a request for help, or an unknown flag
def nu.lhelp(
  hit: Bool,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_long.help(hit, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
  path, binds, pos, raw, seen}):
  match hit:
    case True{}:
      nu.apart(S.parse.take_long.help(True{}, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up,
        subs, path, binds, pos, raw, seen}, ss => nu.help(ss), {==}, hl)
    case False{}:
      nu.apart(S.parse.take_long.help(False{}, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up,
        subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)

# a long option the current command spells, or an unknown one
def nu.found(
  found: Maybe<&2, S.Arg>,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_long.found(found, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0,
  args, up, subs, path, binds, pos, raw, seen}):
  match found:
    case None{}:
      nu.lhelp(S.long_help(name, val, seen), orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hl)
    case Some{aa}:
      nu.arg(Some{aa}, val, orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn)

# a long option with a name
def nu.named(
  empty: Bool,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_long.named(empty, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args,
  up, subs, path, binds, pos, raw, seen}):
  match empty:
    case True{}:
      nu.apart(S.parse.take_long.named(True{}, name, val, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0,
        args, up, subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)
    case False{}:
      nu.found(S.by_long(args, name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn, hl)

# a long option after the `=` cut
def nu.cut(
  nv: String & Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_long.cut(nv, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  match nv:
    case (+name, +val):
      nu.named(String.is_empty(name), name, val, orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn,
        hl)

# a long option
def nu.long(
  +body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_long(body, orig, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  nu.cut(S.cut_eq(body), orig, args, up, subs, path, binds, pos, raw, seen, m0, hd, hn, hl)

# a cluster walker changed from one with `l0` bindings, free: no fewer
# bindings, and failed, waiting, reading a help path, or more bindings
def nu.J(+st: S.St, +l0: Nat) -> Bool:
  Bool.and(Laws.nat_le(l0, nu.blen(st)),
    Bool.or(Bool.or(nu.dead(st), Bool.or(nu.need(st), nu.help(st))), Laws.nat_le(1n+l0, nu.blen(st))))

# a walker that is not free and has no fewer bindings has changed
def nu.j_stop(
  +st: S.St,
  +l0: Nat,
  hb: {Laws.nat_le(l0, nu.blen(st)) == True{} : Bool},
  hs: {Bool.or(nu.dead(st), Bool.or(nu.need(st), nu.help(st))) == True{} : Bool}
) -> {nu.J(st, l0) == True{} : Bool}:
  ee = Equal.sym(Bool, Bool.or(nu.dead(st), Bool.or(nu.need(st), nu.help(st))), True{}, hs)
  %ee : {Bool.and(Laws.nat_le(l0, nu.blen(st)), Bool.or(_, Laws.nat_le(1n+l0, nu.blen(st)))) == True{} : Bool}
  gv.and_tt(Laws.nat_le(l0, nu.blen(st)), True{}, hb, {==})

# a binding changes a cluster walker
def nu.jput(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  gv.and_tt(Laws.nat_le(l0, 1n+List.length(&2, S.Bind, binds)), Laws.nat_le(l0, List.length(&2, S.Bind, binds)),
    nd.le_trans(l0, List.length(&2, S.Bind, binds), 1n+List.length(&2, S.Bind, binds), hl0,
      nd.le_s(List.length(&2, S.Bind, binds))), hl0)

# bound or refused
def nu.jchoice(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  match ok:
    case True{}:
      nu.jput(name, val, args, up, subs, path, binds, pos, raw, seen, l0, hl0)
    case False{}:
      nu.j_stop(S.parse.take_choice(False{}, name, val, args, up, subs, path, binds, pos, raw, seen), l0, hl0, {==})

# an option's value
def nu.jopt_val(
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_opt_val(name, val, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  nu.jchoice(S.allowed(S.parse.choices(S.by_name(args, name)), val), name, val, args, up, subs, path, binds, pos, raw,
    seen, l0, hl0)

# a flag
def nu.jflag(
  val: Maybe<&2, String>,
  +name: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  match val:
    case None{}:
      nu.jput(name, "true", args, up, subs, path, binds, pos, raw, seen, l0, hl0)
    case Some{+vv}:
      nu.j_stop(S.parse.take_flag(Some{vv}, name, orig, args, up, subs, path, binds, pos, raw, seen), l0, hl0, {==})

# an option
def nu.jopt(
  val: Maybe<&2, String>,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  match val:
    case None{}:
      nu.j_stop(S.parse.take_opt(None{}, name, args, up, subs, path, binds, pos, raw, seen), l0, hl0, {==})
    case Some{vv}:
      nu.jopt_val(name, vv, args, up, subs, path, binds, pos, raw, seen, l0, hl0)

# the once-check keeps a changed cluster walker changed
def nu.jonce(
  again: Bool,
  +st: S.St,
  +name: String,
  +path0: List<&2, String>,
  +l0: Nat,
  +hh: {nu.J(st, l0) == True{} : Bool}
) -> {nu.J(S.parse.once(again, st, name, path0), l0) == True{} : Bool}:
  match again:
    case True{}:
      match st:
        case S.St{+mm, +aa, +gg, +ss, +pp, +bb, +oo, +rr, +nn}:
          nu.j_stop(S.parse.once(True{}, S.St{mm, aa, gg, ss, pp, bb, oo, rr, nn}, name, path0), l0,
            gv.and_l(Laws.nat_le(l0, List.length(&2, S.Bind, bb)),
              Bool.or(Bool.or(nu.dead_m(mm), Bool.or(nu.need_m(mm), nu.help_m(mm))),
                Laws.nat_le(1n+l0, List.length(&2, S.Bind, bb))), hh), {==})
    case False{}:
      hh

# a found argument, by its kind
def nu.jakind(
  kk: S.ArgKind,
  +name: String,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_arg.kind(kk, name, val, orig, args, up, subs, path, binds, pos, raw, seen),
  l0) == True{} : Bool}:
  match kk:
    case S.Flag{}:
      nu.jonce(S.bound(binds, name), S.parse.take_flag(val, name, orig, args, up, subs, path, binds, pos, raw, seen),
        name, path, l0, nu.jflag(val, name, orig, args, up, subs, path, binds, pos, raw, seen, l0, hl0))
    case S.Opt{}:
      nu.jonce(S.bound(binds, name), S.parse.take_opt(val, name, args, up, subs, path, binds, pos, raw, seen),
        name, path, l0, nu.jopt(val, name, args, up, subs, path, binds, pos, raw, seen, l0, hl0))
    case S.Many{}:
      nu.jopt(val, name, args, up, subs, path, binds, pos, raw, seen, l0, hl0)
    case S.Pos{}:
      nu.j_stop(S.parse.take_arg.kind(S.Pos{}, name, val, orig, args, up, subs, path, binds, pos, raw, seen), l0, hl0,
        {==})
    case S.Rest{}:
      nu.j_stop(S.parse.take_arg.kind(S.Rest{}, name, val, orig, args, up, subs, path, binds, pos, raw, seen), l0,
        hl0, {==})

# a found argument, or an unknown flag
def nu.jarg(
  found: Maybe<&2, S.Arg>,
  +val: Maybe<&2, String>,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.parse.take_arg(found, val, orig, args, up, subs, path, binds, pos, raw, seen), l0) == True{} : Bool}:
  match found:
    case None{}:
      nu.j_stop(S.parse.take_arg(None{}, val, orig, args, up, subs, path, binds, pos, raw, seen), l0, hl0, {==})
    case Some{aa}:
      match aa:
        case S.Arg{+name, _s, _l, kind, _h, _r, _d, _c}:
          nu.jakind(kind, name, val, orig, args, up, subs, path, binds, pos, raw, seen, l0, hl0)

# one letter, by the walker's mode
def nu.jmode(
  mode: S.Mode,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +l0: Nat,
  +hl0: {Laws.nat_le(l0, List.length(&2, S.Bind, binds)) == True{} : Bool}
) -> {nu.J(S.cluster.apply.mode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen),
  l0) == True{} : Bool}:
  match mode:
    case S.Dead{+ee}:
      nu.j_stop(S.St{S.Dead{ee}, args, up, subs, path, binds, pos, raw, seen}, l0, hl0, {==})
    case S.Free{}:
      nu.jarg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, l0, hl0)
    case S.Need{_n}:
      nu.jarg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, l0, hl0)
    case S.Help{}:
      nu.jarg(S.by_short(args, SCon{cc, SNil{}}), S.cluster.val(S.by_short(args, SCon{cc, SNil{}}), rest), orig, args,
        up, subs, path, binds, pos, raw, seen, l0, hl0)

# one letter against a walker with no fewer bindings than the start
def nu.japply(
  st: S.St,
  +cc: Char,
  +rest: String,
  +orig: String,
  +l0: Nat,
  +hb: {Laws.nat_le(l0, nu.blen(st)) == True{} : Bool}
) -> {nu.J(S.cluster.apply(st, cc, rest, orig), l0) == True{} : Bool}:
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      nu.jmode(mode, cc, rest, orig, args, up, subs, path, binds, pos, raw, seen, l0, hb)

# a changed walker has no fewer bindings
def nu.j_le(
  +st: S.St,
  +l0: Nat,
  +hh: {nu.J(st, l0) == True{} : Bool}
) -> {Laws.nat_le(l0, nu.blen(st)) == True{} : Bool}:
  gv.and_l(Laws.nat_le(l0, nu.blen(st)),
    Bool.or(Bool.or(nu.dead(st), Bool.or(nu.need(st), nu.help(st))), Laws.nat_le(1n+l0, nu.blen(st))), hh)

# a letter keeps a changed walker changed
def nu.jletter(
  done: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  +st: S.St,
  +l0: Nat,
  +hh: {nu.J(st, l0) == True{} : Bool}
) -> {nu.J(S.cluster.letter(done, cc, rest, orig, st), l0) == True{} : Bool}:
  match done:
    case True{}:
      hh
    case False{}:
      nu.japply(st, cc, rest, orig, l0, nu.j_le(st, l0, hh))

# the rest of a cluster keeps a changed walker changed
def nu.jcluster(
  body: String,
  +orig: String,
  +st: S.St,
  +done: Bool,
  +l0: Nat,
  +hh: {nu.J(st, l0) == True{} : Bool}
) -> {nu.J(S.cluster(body, orig, st, done), l0) == True{} : Bool}:
  match body:
    case SNil{}:
      hh
    case SCon{+cc, +rest}:
      nu.jcluster(rest, orig, S.cluster.letter(done, cc, rest, orig, st), S.cluster.done(done, cc, rest, st), l0,
        nu.jletter(done, cc, rest, orig, st, l0, hh))

# a count is never above itself by one
def nu.le_sn(nn: Nat) -> {Laws.nat_le(1n+nn, nn) == False{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+pp:
      nu.le_sn(pp)

# a cluster of at least one letter changes the walker
def nu.cluster1(
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, binds, pos, False{}, seen},
  False{}), S.St{m0, args, up, subs, path, binds, pos, False{}, seen}):
  +l0 = List.length(&2, S.Bind, binds)
  +s0 = {S.St{S.Free{}, args, up, subs, path, binds, pos, False{}, seen} : S.St}
  +fin = S.cluster(SCon{cc, rest}, orig, s0, False{})
  hj = nu.jcluster(rest, orig, S.cluster.letter(False{}, cc, rest, orig, s0), S.cluster.done(False{}, cc, rest, s0), l0,
    nu.japply(s0, cc, rest, orig, l0, nd.le_refl(l0)))
  e1 = Equal.sym(Bool, nu.dead_m(m0), False{}, hd)
  e2 = Equal.sym(Bool, nu.need_m(m0), False{}, hn)
  e3 = Equal.sym(Bool, nu.help_m(m0), False{}, hl)
  e4 = Equal.sym(Bool, Laws.nat_le(l0, l0), True{}, nd.le_refl(l0))
  e5 = Equal.sym(Bool, Laws.nat_le(1n+l0, l0), False{}, nu.le_sn(l0))
  jo = {%e1 : {Bool.and(Laws.nat_le(l0, l0), Bool.or(Bool.or(_, Bool.or(nu.need_m(m0), nu.help_m(m0))),
      Laws.nat_le(1n+l0, l0))) == False{} : Bool}
    %e2 : {Bool.and(Laws.nat_le(l0, l0), Bool.or(Bool.or(False{}, Bool.or(_, nu.help_m(m0))),
      Laws.nat_le(1n+l0, l0))) == False{} : Bool}
    %e3 : {Bool.and(Laws.nat_le(l0, l0), Bool.or(Bool.or(False{}, Bool.or(False{}, _)),
      Laws.nat_le(1n+l0, l0))) == False{} : Bool}
    %e4 : {Bool.and(_, Laws.nat_le(1n+l0, l0)) == False{} : Bool}
    %e5 : {_ == False{} : Bool}
    {==} : {nu.J(S.St{m0, args, up, subs, path, binds, pos, False{}, seen}, l0) == False{} : Bool}}
  nu.apart(fin, S.St{m0, args, up, subs, path, binds, pos, False{}, seen}, ss => nu.J(ss, l0), hj, jo)

# a nonempty short option body: a request for help, or a cluster
def nu.sgo(
  hit: Bool,
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_short.go(hit, SCon{cc, rest}, orig, args, up, subs, path, binds, pos, False{}, seen),
    S.St{m0, args, up, subs, path, binds, pos, False{}, seen}):
  match hit:
    case True{}:
      nu.apart(S.parse.take_short.go(True{}, SCon{cc, rest}, orig, args, up, subs, path, binds, pos, False{}, seen),
        S.St{m0, args, up, subs, path, binds, pos, False{}, seen}, ss => nu.help(ss), {==}, hl)
    case False{}:
      nu.cluster1(cc, rest, orig, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl)

# a nonempty cluster body is a char in front of the rest
def nu.cl0(
  body: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool},
  +he: {String.is_empty(body) == False{} : Bool}
) -> nu.N(S.parse.take_short(body, orig, args, up, subs, path, binds, pos, False{}, seen),
    S.St{m0, args, up, subs, path, binds, pos, False{}, seen}):
  match body:
    case SNil{}:
      Empty.absurd(nu.N(S.parse.take_short(SNil{}, orig, args, up, subs, path, binds, pos, False{}, seen),
        S.St{m0, args, up, subs, path, binds, pos, False{}, seen}), Walk.wk.true_false(he))
    case SCon{+cc, +rest}:
      nu.sgo(S.short_help(SCon{cc, rest}, args, seen), cc, rest, orig, args, up, subs, path, binds, pos, seen, m0, hd,
        hn, hl)

# a value bound or refused, against any walker with as many bindings that has
# not failed
def nu.choice_any(
  ok: Bool,
  +name: String,
  +val: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +orig: S.St,
  +hb: {nu.blen(orig) == List.length(&2, S.Bind, binds) : Nat},
  +hd: {nu.dead(orig) == False{} : Bool}
) -> nu.N(S.parse.take_choice(ok, name, val, args, up, subs, path, binds, pos, raw, seen), orig):
  match ok:
    case True{}:
      nu.more(S.parse.put(name, val, args, up, subs, path, binds, pos, raw, seen), orig, List.length(&2, S.Bind, binds),
        {==}, hb)
    case False{}:
      nu.apart(S.parse.take_choice(False{}, name, val, args, up, subs, path, binds, pos, raw, seen), orig,
        ss => nu.dead(ss), {==}, hd)

# a positional binds the word, or none is left
def nu.take_pos(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.take_pos(tok, args, up, subs, path, binds, pos, raw), S.St{m0, args, up, subs, path, binds, pos,
  raw, seen}):
  match pos:
    case Nil{}:
      nu.apart(S.parse.take_pos(tok, args, up, subs, path, binds, [], raw), S.St{m0, args, up, subs, path, binds, [],
        raw, seen},
        ss => nu.dead(ss), {==}, hd)
    case Con{ph, +tt}:
      match ph:
        case S.Arg{+name, +sh, +lo, +kind, +hl, +req, +dd, +cs}:
          nu.choice_any(S.allowed(cs, tok), name, tok, args, up, subs, path, binds,
            S.parse.take_pos.keep(S.rest.is(S.Arg{name, sh, lo, kind, hl, req, dd, cs}),
              S.Arg{name, sh, lo, kind, hl, req, dd, cs}, tt), raw, True{},
            S.St{m0, args, up, subs, path, binds, S.Arg{name, sh, lo, kind, hl, req, dd, cs} <> tt, raw,
              seen}, {==}, hd)

# entering a subcommand adds a level
def nu.enter(
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode
) -> nu.N(S.parse.enter(ss, args, up, path, binds), S.St{m0, args, up, subs, path, binds, pos, raw, seen}):
  match ss:
    case S.Sub{+nn, +na, +nx, +nc}:
      nu.deeper(S.parse.enter(S.Sub{nn, na, nx, nc}, args, up, path, binds), S.St{m0, args, up, subs, path, binds,
        pos, raw, seen},
        List.length(&2, S.Level, up), {==}, {==})

# a subcommand entered, or a missing positional
def nu.enter_or(
  miss: Maybe<&2, String>,
  ss: S.Sub,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.enter_or(miss, ss, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  match miss:
    case None{}:
      nu.enter(ss, args, up, subs, path, binds, pos, raw, seen, m0)
    case Some{+nn}:
      nu.apart(S.parse.enter_or(Some{nn}, ss, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
        path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)

# a word
def nu.word_go(
  found: Maybe<&2, S.Sub>,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.word.go(found, tok, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path,
  binds, pos, raw, seen}):
  match found:
    case None{}:
      nu.take_pos(tok, args, up, subs, path, binds, pos, raw, seen, m0, hd)
    case Some{ss}:
      nu.enter_or(S.parse.first_req(pos), ss, args, up, subs, path, binds, pos, raw, seen, m0, hd)

# a word
def nu.word(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.word(tok, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs, path, binds, pos,
  raw, seen}):
  nu.word_go(S.find_sub(subs, tok), tok, args, up, subs, path, binds, pos, raw, seen, m0, hd)

# `-` alone, or a cluster
def nu.short_go(
  alone: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool},
  +ha: {String.is_empty(String.drop(tok, 1n)) == alone : Bool}
) -> nu.N(S.parse.step.short.go(alone, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path,
  binds, pos, False{}, seen}):
  match alone:
    case True{}:
      nu.word(tok, args, up, subs, path, binds, pos, False{}, seen, m0, hd)
    case False{}:
      nu.cl0(String.drop(tok, 1n), tok, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl, ha)

# a short option or a word
def nu.step_short(
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.short(dash, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path, binds,
  pos, False{}, seen}):
  match dash:
    case True{}:
      nu.short_go(String.is_empty(String.drop(tok, 1n)), tok, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl,
        {==})
    case False{}:
      nu.word(tok, args, up, subs, path, binds, pos, False{}, seen, m0, hd)

# a long option, a short one, or a word
def nu.kind_go(
  long: Bool,
  dash: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.kind.go(long, dash, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs,
  path, binds, pos, False{}, seen}):
  match long:
    case True{}:
      nu.long(String.drop(tok, 2n), tok, args, up, subs, path, binds, pos, False{}, seen, m0, hd, hn, hl)
    case False{}:
      nu.step_short(dash, tok, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl)

# a word by its shape
def nu.skind(
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.kind(tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path, binds, pos,
  False{}, seen}):
  nu.kind_go(String.starts_with(tok, "--"), String.starts_with(tok, "-"), tok, args, up, subs, path, binds, pos, seen,
    m0,
    hd, hn, hl)

# `help` starts a help path
def nu.help_w(
  hit: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.help(hit, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path, binds,
  pos, False{}, seen}):
  match hit:
    case True{}:
      nu.apart(S.parse.step.help(True{}, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path,
        binds, pos, False{}, seen}, ss => nu.help(ss), {==}, hl)
    case False{}:
      nu.skind(tok, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl)

# `--` switches to positionals
def nu.end(
  end: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.end(end, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path, binds,
  pos, False{}, seen}):
  match end:
    case True{}:
      nu.apart(S.parse.step.end(True{}, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path,
        binds, pos, False{}, seen}, ss => nu.raw(ss), {==}, {==})
    case False{}:
      nu.help_w(Bool.and(String.eq(tok, "help"), Bool.not(seen)), tok, args, up, subs, path, binds, pos, seen, m0, hd,
        hn,
        hl)

# after `--` a word is a positional
def nu.rawf(
  raw: Bool,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool},
  +hn: {nu.need_m(m0) == False{} : Bool},
  +hl: {nu.help_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.raw(raw, tok, args, up, subs, path, binds, pos, seen), S.St{m0, args, up, subs, path, binds,
  pos, raw, seen}):
  match raw:
    case True{}:
      nu.take_pos(tok, args, up, subs, path, binds, pos, True{}, seen, m0, hd)
    case False{}:
      nu.end(String.eq(tok, "--"), tok, args, up, subs, path, binds, pos, seen, m0, hd, hn, hl)

# a waiting option binds the word, or refuses it
def nu.need_w(
  flag: Bool,
  +name: String,
  +tok: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +binds: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +m0: S.Mode,
  +hd: {nu.dead_m(m0) == False{} : Bool}
) -> nu.N(S.parse.step.need(flag, name, tok, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up, subs,
  path, binds, pos, raw, seen}):
  match flag:
    case True{}:
      nu.apart(S.parse.step.need(True{}, name, tok, args, up, subs, path, binds, pos, raw, seen), S.St{m0, args, up,
        subs, path, binds, pos, raw, seen}, ss => nu.dead(ss), {==}, hd)
    case False{}:
      nu.opt_val(name, tok, args, up, subs, path, binds, pos, raw, seen, m0, hd)

def Laws.word_used(tok, st, h_live, h_same):
  match st:
    case S.St{mode, +args, +up, +subs, +path, +binds, +pos, +raw, +seen}:
      match mode:
        case S.Dead{+ee}:
          Walk.wk.false_true(h_live)
        case S.Help{}:
          Walk.wk.false_true(h_live)
        case S.Need{+nn}:
          nu.need_w(S.looks_flag(tok), nn, tok, args, up, subs, path, binds, pos, raw, seen, S.Need{nn}, {==}, h_same)
        case S.Free{}:
          nu.rawf(raw, tok, args, up, subs, path, binds, pos, seen, S.Free{}, {==}, {==}, {==}, h_same)
