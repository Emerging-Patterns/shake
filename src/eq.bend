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
def bool_cmp_self(bb):
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
def word_cmp_self(nn, ww):
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
def u32_cmp_self(uu):
  match uu:
    case U32{+ww}:
      word_cmp_self(32n, ww)

# LAW: a char compares equal to itself
law char_cmp_self:
  for +cc: Char
  {Char.cmp(cc, cc) == ((cc, cc), EQ{}) : (Char & Char) & Cmp}

# a char is a code point, and the pair it is compared inside rides along
def char_cmp_self(cc):
  match cc:
    case Chr{+xx}:
      Equal.cong(Cmp, (Char & Char) & Cmp, rr => ((Chr{xx}, Chr{xx}), rr),
        U32.cmp(xx, xx), EQ{}, u32_cmp_self(xx))

# LAW: a string compares equal to itself
law string_cmp_self:
  for +ss: String
  {String.cmp(ss, ss) == ((ss, ss), EQ{}) : (String & String) & Cmp}

# by induction on the string: the head's law and the tail's, composed the
# way String.cmp composes them
def string_cmp_self(ss):
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

# equality is the comparison read as a bit, so the comparison's law answers
def string_eq_self(ss):
  Equal.cong((String & String) & Cmp, Bool, rr => String.eq.fin(rr),
    String.cmp(ss, ss), ((ss, ss), EQ{}), string_cmp_self(ss))
