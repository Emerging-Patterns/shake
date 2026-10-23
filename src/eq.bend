# shake/eq: the Base facts a proof needs and Base does not state, taken from
# ez's check/eq.bend. A string equals itself: every lookup in shake asks
# whether a name it just bound is the name it is looking for, so the proofs
# need that answer to be yes rather than assume it.
import Base

# LAW: a bit compares equal to itself
law bool_cmp_self:
  for +bb: Bool
  {Bool.cmp(bb, bb) == EQ{} : Cmp}

# the two bits, each compared with itself
def bool_cmp_self(bb):  # noqa: L001 a proof of this file's law
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# LAW: a word compares equal to itself
law word_cmp_self:
  for nn: Nat
  for +ww: Word(nn)
  {Word.cmp(nn, ww, ww) == EQ{} : Cmp}

# by induction on the width: a word of no bits and a bit carried over one
def word_cmp_self(nn, ww):  # noqa: L001 a proof of this file's law
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Cmp, Word.cmp.fin(bb, bb, Word.cmp(pp, tt, tt)),
            Word.cmp.fin(bb, bb, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, cc => Word.cmp.fin(bb, bb, cc),
              Word.cmp(pp, tt, tt), EQ{}, word_cmp_self(pp, tt)),
            bool_cmp_self(bb))

# LAW: a number compares equal to itself
law u32_cmp_self:
  for +uu: U32
  {U32.cmp(uu, uu) == EQ{} : Cmp}

# a number is a word of thirty-two bits, so the word's law answers for it
def u32_cmp_self(uu):  # noqa: L001 a proof of this file's law
  match uu:
    case U32{+ww}:
      word_cmp_self(32n, ww)

# LAW: a char compares equal to itself
law char_cmp_self:
  for +cc: Char
  {Char.cmp(cc, cc) == ((cc, cc), EQ{}) : (Char & Char) & Cmp}

# a char is a code point, and the pair it is compared inside rides along
def char_cmp_self(cc):  # noqa: L001 a proof of this file's law
  match cc:
    case Chr{+xx}:
      Equal.cong(Cmp, (Char & Char) & Cmp, rr => ((Chr{xx}, Chr{xx}), rr),
        U32.cmp(xx, xx), EQ{}, u32_cmp_self(xx))

# LAW: a char equals itself
law char_eq_self:
  for +cc: Char
  {Char.is_eq(cc, cc) == True{} : Bool}

# a char is a code point, and equality is the comparison's verdict
def char_eq_self(cc):  # noqa: L001 a proof of this file's law
  match cc:
    case Chr{+xx}:
      Equal.cong(Cmp, Bool, rr => Cmp.is_eq(rr), U32.cmp(xx, xx), EQ{}, u32_cmp_self(xx))

# LAW: a string compares equal to itself
law string_cmp_self:
  for +ss: String
  {String.cmp(ss, ss) == ((ss, ss), EQ{}) : (String & String) & Cmp}

# by induction on the string: the head's law and the tail's, composed the
# way String.cmp composes them
def string_cmp_self(ss):  # noqa: L001 a proof of this file's law
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.trans((String & String) & Cmp,
        String.cmp.fin(tt, tt, Char.cmp(hh, hh)),
        String.cmp.rec(hh, hh, String.cmp(tt, tt)),
        ((SCon{hh, tt}, SCon{hh, tt}), EQ{}),
        Equal.cong((Char & Char) & Cmp, (String & String) & Cmp,
          hc => String.cmp.fin(tt, tt, hc), Char.cmp(hh, hh), ((hh, hh), EQ{}),
          char_cmp_self(hh)),
        Equal.cong((String & String) & Cmp, (String & String) & Cmp,
          rr => String.cmp.rec(hh, hh, rr), String.cmp(tt, tt), ((tt, tt), EQ{}),
          string_cmp_self(tt)))

# LAW: a string equals itself
law string_eq_self:
  for +ss: String
  {String.eq(ss, ss) == True{} : Bool}

# LAW: a string orders equal to itself
law string_order_self:
  for +ss: String
  {String.order.go(ss, ss, EQ{}) == EQ{} : Cmp}

# by induction on the string: the head's code point compares equal to itself,
# so the walk goes on to the tail still equal
def string_order_self(ss):  # noqa: L001 a proof of this file's law
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(Cmp, String.order.go(tt, tt, U32.cmp(xx, xx)),
            String.order.go(tt, tt, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, cc => String.order.go(tt, tt, cc),
              U32.cmp(xx, xx), EQ{}, u32_cmp_self(xx)),
            string_order_self(tt))

# equality is the order's verdict read as a bit, so the order's law answers
def string_eq_self(ss):  # noqa: L001 a proof of this file's law
  Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc),
    String.order.go(ss, ss, EQ{}), EQ{}, string_order_self(ss))

# LAW: an order already decided below stays below, whatever is left
law string_order_lt:
  for +aa: String
  for +bb: String
  {String.order.go(aa, bb, LT{}) == LT{} : Cmp}

# the walk only goes on while the order is equal
def string_order_lt(aa, bb):  # noqa: L001 a proof of this file's law
  match aa:
    case SNil{}:
      match bb:
        case SNil{}:
          {==}
        case SCon{+_kk, +_ut}:
          {==}
    case SCon{+hh, +_tt}:
      match hh:
        case Chr{+_xx}:
          match bb:
            case SNil{}:
              {==}
            case SCon{+kk, +_ut}:
              match kk:
                case Chr{+_yy}:
                  {==}

# LAW: an order already decided above stays above, whatever is left
law string_order_gt:
  for +aa: String
  for +bb: String
  {String.order.go(aa, bb, GT{}) == GT{} : Cmp}

# the walk only goes on while the order is equal
def string_order_gt(aa, bb):  # noqa: L001 a proof of this file's law
  match aa:
    case SNil{}:
      match bb:
        case SNil{}:
          {==}
        case SCon{+_kk, +_ut}:
          {==}
    case SCon{+hh, +_tt}:
      match hh:
        case Chr{+_xx}:
          match bb:
            case SNil{}:
              {==}
            case SCon{+kk, +_ut}:
              match kk:
                case Chr{+_yy}:
                  {==}

# Soundness, taken from ez's check/str.bend: a comparison that answered
# equal was given one thing twice.

# the type that is empty exactly where a bit is True
def bit.emp(flag: Bool) -> Type:
  match flag:
    case False{}:
      Unit
    case True{}:
      Empty

def bit.clash(eq: {False{} == True{} : Bool}) -> Empty:
  %eq : bit.emp(_)
  Unit{}

def bit.gone(a, -A: Kind(a), never: Empty) -> A:
  match never:

def bit.absurd(a, -A: Kind(a), eq: {False{} == True{} : Bool}) -> A:
  bit.gone(a, A, bit.clash(eq))

# and the same read the other way round
def bit.emp2(flag: Bool) -> Type:
  match flag:
    case False{}:
      Empty
    case True{}:
      Unit

def bit.clash2(eq: {True{} == False{} : Bool}) -> Empty:
  %eq : bit.emp2(_)
  Unit{}

def bit.absurd2(a, -A: Kind(a), eq: {True{} == False{} : Bool}) -> A:
  bit.gone(a, A, bit.clash2(eq))


# Equality. Base compares a char as a 32-bit word and a string char by char,
# and states no fact that a comparison which answered equal was given one
# thing twice. Two words that compare equal are one word by induction on the
# width, and two strings by induction on the string.

# the type that is empty exactly where a comparison answered EQ
def cmp.emp(ans: Cmp) -> Type:
  match ans:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def cmp.lt(eq: {LT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

def cmp.gt(eq: {GT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

# LAW: a comparison that reads as equal is EQ
law cmp_is_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

# the two other answers read as False
def cmp_is_eq(c, e):  # noqa: L001 a proof of this file's law
  match c:
    case LT{}:
      bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
    case EQ{}:
      {==}
    case GT{}:
      bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two bits that compare equal are one bit
law bool_eq:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

# the two bits that differ compare LT or GT
def bool_eq(a, b, e):  # noqa: L001 a proof of this file's law
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      bit.gone(&2, {False{} == True{} : Bool}, cmp.lt(e))
    case True{} False{}:
      bit.gone(&2, {True{} == False{} : Bool}, cmp.gt(e))
    case True{} True{}:
      {==}

# LAW: a word comparison that ends EQ had tails that compared EQ
law fin_tail:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

# an answer of LT or GT from the tails is the answer, never EQ
def fin_tail(_ab, _bb, t, e):  # noqa: L001 a proof of this file's law
  match t:
    case LT{}:
      bit.gone(&2, {LT{} == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      {==}
    case GT{}:
      bit.gone(&2, {GT{} == EQ{} : Cmp}, cmp.gt(e))

# LAW: and heads that compared EQ
law fin_head:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {Bool.cmp(ab, bb) == EQ{} : Cmp}

# and an EQ from the tails leaves the heads to answer
def fin_head(ab, bb, t, e):  # noqa: L001 a proof of this file's law
  match t:
    case LT{}:
      bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      e
    case GT{}:
      bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.gt(e))

# LAW: two words that compare equal are one word
law word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

# by induction on the width: the heads by the bit law, then the tails
def word_eq(n, a, b, e):  # noqa: L001 a proof of this file's law
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Word(1n+p), WCon{ab, at}, WCon{bb, at}, WCon{bb, bt},
            Equal.cong(Bool, Word(1n+p), x => WCon{x, at}, ab, bb,
              bool_eq(ab, bb, fin_head(ab, bb, Word.cmp(p, at, bt), e))),
            Equal.cong(Word(p), Word(1n+p), y => WCon{bb, y}, at, bt,
              word_eq(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), e))))

# LAW: two code points that compare equal are one char
law u32_eq:
  for x: U32
  for y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {Chr{x} == Chr{y} : Char}

# a code point is a word of thirty-two bits
def u32_eq(x, y, e):  # noqa: L001 a proof of this file's law
  match x y:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), Char, w => Chr{U32{w}}, wx, wy,
        word_eq(32n, wx, wy, cmp_is_eq(Word.cmp(32n, wx, wy), e)))

# LAW: two chars that compare equal are one char
law char_eq_true:
  for a: Char
  for b: Char
  for e: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

# a char is a code point
def char_eq_true(a, b, e):  # noqa: L001 a proof of this file's law
  match a b:
    case Chr{x} Chr{y}:
      u32_eq(x, y, e)

# LAW: a string comparison read as a bit reads only the comparison, so the
# chars it rebuilt in front do not change it
law eq_fin_rec:
  for h1: Char
  for h2: Char
  for r: (String & String) & Cmp
  {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, r)))
    == Cmp.is_eq(Pair.snd(String & String, Cmp, r)) : Bool}

# the comparison, taken apart and put back together
def eq_fin_rec(_h1, _h2, r):  # noqa: L001 a proof of this file's law
  match r:
    case (ts, c):
      match ts:
        case (t1, t2):
          {==}

# LAW: two strings that read as equal, whose heads compared as the given
# answer, have one head. The answer is a parameter so that the arms it did not
# take can be closed.
law eq_head.cmp:
  for +x: U32
  for +y: U32
  for t1: String
  for t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for e: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))))
    == True{} : Bool}
  {Chr{x} == Chr{y} : Char}

def eq_head.cmp(x, y, _t1, _t2, c, ec, e):
  match c:
    case LT{}:
      bit.absurd(&2, {Chr{x} == Chr{y} : Char}, e)
    case EQ{}:
      u32_eq(x, y, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), U32.cmp(x, y),
        EQ{}, ec))
    case GT{}:
      bit.absurd(&2, {Chr{x} == Chr{y} : Char}, e)

# LAW: two strings that compare equal by String.cmp are one string
law cmp_true:
  for a: String
  for b: String
  for +e: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(a, b))) == True{} : Bool}
  {a == b : String}

# LAW: the tails of two strings with a first char each that compare equal
# compare equal: the chars rebuilt in front do not change the answer
law cmp_tail.cmp:
  for x: U32
  for y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for e: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))))
    == True{} : Bool}
  {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))) == True{} : Bool}

# the old eq_tail.cmp's argument, stopped at the comparison
def cmp_tail.cmp(x, y, t1, t2, c, _ec, e):
  match c:
    case LT{}:
      bit.absurd(&2, {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))) == True{} : Bool}, e)
    case EQ{}:
      Equal.trans(Bool,
        Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))),
        Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2)))),
        True{},
        Equal.sym(Bool,
          Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2)))),
          Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))),
          eq_fin_rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        e)
    case GT{}:
      bit.absurd(&2, {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp(t1, t2))) == True{} : Bool}, e)

# by induction on both strings, as string_eq_true goes over String.eq
def cmp_true(a, b, e):  # noqa: L001 a proof of this file's law
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      bit.absurd(&2, {SNil{} == SCon{h, t} : String}, e)
    case SCon{h, t} SNil{}:
      bit.absurd(&2, {SCon{h, t} == SNil{} : String}, e)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
          Equal.trans(String, SCon{Chr{x}, t1}, SCon{Chr{y}, t1}, SCon{Chr{y}, t2},
            Equal.cong(Char, String, h => SCon{h, t1}, Chr{x}, Chr{y},
              eq_head.cmp(x, y, t1, t2, U32.cmp(x, y), {==}, e)),
            Equal.cong(String, String, t => SCon{Chr{y}, t}, t1, t2,
              cmp_true(t1, t2, cmp_tail.cmp(x, y, t1, t2, U32.cmp(x, y), {==}, e))))

# LAW: and tails that read as equal
law eq_tail.cmp:
  for x: U32
  for y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for e: {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))))
    == True{} : Bool}
  {String.eq(t1, t2) == True{} : Bool}

# the tails compare equal, so they are one string, which equals itself
def eq_tail.cmp(x, y, t1, t2, c, ec, e):
  Equal.trans(Bool, String.eq(t1, t2), String.eq(t1, t1), True{},
    Equal.cong(String, Bool, t => String.eq(t1, t), t2, t1,
      Equal.sym(String, t1, t2, cmp_true(t1, t2, cmp_tail.cmp(x, y, t1, t2, c, ec, e)))),
    string_eq_self(t1))

# LAW: a walk in order that ends equal began equal: from LT or GT it never
# moves
law order_start:
  for a: String
  for b: String
  for c: Cmp
  for e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}
  {c == EQ{} : Cmp}

# every arm the walk takes on a start other than EQ answers that start
def order_start(a, b, c, e):  # noqa: L001 a proof of this file's law
  match a b:
    case SNil{} SNil{}:
      cmp_is_eq(c, e)
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          {==}
        case GT{}:
          bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{x}, t} SNil{}:
      match c:
        case LT{}:
          bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          {==}
        case GT{}:
          bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          match c:
            case LT{}:
              bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
            case EQ{}:
              {==}
            case GT{}:
              bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two strings with a first char each, which read as equal, have one
# first char
law eq_head:
  for h1: Char
  for h2: Char
  for +t1: String
  for +t2: String
  for e: {String.eq(SCon{h1, t1}, SCon{h2, t2}) == True{} : Bool}
  {h1 == h2 : Char}

# the walk goes on to the tails from the heads' comparison, which must have
# been EQ for the walk to end equal
def eq_head(h1, h2, t1, t2, e):  # noqa: L001 a proof of this file's law
  match h1 h2:
    case Chr{+x} Chr{+y}:
      u32_eq(x, y, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), U32.cmp(x, y), EQ{},
        order_start(t1, t2, U32.cmp(x, y), e)))

# LAW: and the rest of each reads as equal
law eq_tail:
  for h1: Char
  for h2: Char
  for +t1: String
  for +t2: String
  for +e: {String.eq(SCon{h1, t1}, SCon{h2, t2}) == True{} : Bool}
  {String.eq(t1, t2) == True{} : Bool}

# and the walk over the tails started from that EQ
def eq_tail(h1, h2, t1, t2, e):  # noqa: L001 a proof of this file's law
  match h1 h2:
    case Chr{+x} Chr{+y}:
      Equal.trans(Bool, String.eq(t1, t2),
        Cmp.is_eq(String.order.go(t1, t2, U32.cmp(x, y))), True{},
        Equal.cong(Cmp, Bool, k => Cmp.is_eq(String.order.go(t1, t2, k)), EQ{}, U32.cmp(x, y),
          Equal.sym(Cmp, U32.cmp(x, y), EQ{}, order_start(t1, t2, U32.cmp(x, y), e))),
        e)

# LAW: two strings that compare equal are one string
law string_eq_true:
  for a: String
  for b: String
  for +e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

# by induction on both strings: two of different lengths never read as
# equal, and two with a first char each have one head and equal tails
def string_eq_true(a, b, e):  # noqa: L001 a proof of this file's law
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      bit.absurd(&2, {SNil{} == SCon{h, t} : String}, e)
    case SCon{Chr{x}, t} SNil{}:
      bit.absurd(&2, {SCon{Chr{x}, t} == SNil{} : String}, e)
    case SCon{+h1, +t1} SCon{+h2, +t2}:
      Equal.trans(String, SCon{h1, t1}, SCon{h2, t1}, SCon{h2, t2},
        Equal.cong(Char, String, h => SCon{h, t1}, h1, h2,
          eq_head(h1, h2, t1, t2, e)),
        Equal.cong(String, String, t => SCon{h2, t}, t1, t2,
          string_eq_true(t1, t2, eq_tail(h1, h2, t1, t2, e))))
