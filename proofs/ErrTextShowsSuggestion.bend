# proofs of laws/ErrTextShowsSuggestion.bend
import Base
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../laws/ErrTextShowsSuggestion.bend as Laws
import ../laws/PrefixEmpty.bend as L1
import ./lemmas/WalkSteps.bend as M1

# that `qq` contains `ss`
def ct.has(qq: String, ss: String) -> Type:
  {String.contains(qq, ss) == True{} : Bool}

# appending is associative
def ct.assoc(aa: String, +bb: String, +cc: String) -> {(aa ++ bb) ++ cc == aa ++ (bb ++ cc) : String}:
  match aa:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, ys => SCon{hh, ys}, (tt ++ bb) ++ cc, tt ++ (bb ++ cc), ct.assoc(tt, bb, cc))

# a string starts with itself, whatever follows
def ct.starts(ss: String, +post: String) -> {String.starts_with(ss ++ post, ss) == True{} : Bool}:
  match ss:
    case SNil{}:
      L1.prefix_empty(post)
    case SCon{+hh, tt}:
      e1 = Equal.sym(Bool, Char.is_eq(hh, hh), True{}, Eq.char_eq_self(hh))
      %e1 : {String.starts_with.go.if(tt, tt ++ post, _) == True{} : Bool}
      ct.starts(tt, post)

# every string contains the empty one
def ct.nil(post: String) -> ct.has(post, ""):
  match post:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# a string contains itself, whatever follows
def ct.front(ss: String, +post: String) -> ct.has(ss ++ post, ss):
  match ss:
    case SNil{}:
      ct.nil(post)
    case SCon{+hh, +tt}:
      e1 = Equal.sym(Bool, String.starts_with(SCon{hh, tt ++ post}, SCon{hh, tt}), True{},
        ct.starts(SCon{hh, tt}, post))
      %e1 : {String.contains.if(tt ++ post, SCon{hh, tt}, _) == True{} : Bool}
      {==}

# a contained string stays contained, here or further on
def ct.if(
  tt: String,
  +ss: String,
  here: Bool,
  hh: ct.has(tt, ss)
) -> {String.contains.if(tt, ss, here) == True{} : Bool}:
  match here:
    case False{}:
      hh
    case True{}:
      {==}

# what a string contains, it contains after anything
def ct.after(pre: String, +qq: String, +ss: String, hh: ct.has(qq, ss)) -> ct.has(pre ++ qq, ss):
  match pre:
    case SNil{}:
      hh
    case SCon{+ch, +tt}:
      ct.if(tt ++ qq, ss, String.starts_with(SCon{ch, tt ++ qq}, ss), ct.after(tt, qq, ss, hh))

# a string contained in the part after `pp` is contained in the whole
def ct.step(
  +pp: String,
  +qq: String,
  +rr: String,
  +ss: String,
  hh: ct.has(qq ++ rr, ss)
) -> ct.has((pp ++ qq) ++ rr, ss):
  e1 = Equal.sym(String, (pp ++ qq) ++ rr, pp ++ (qq ++ rr), ct.assoc(pp, qq, rr))
  %e1 : {String.contains(_, ss) == True{} : Bool}
  ct.after(pp, qq ++ rr, ss, hh)

# a string is contained where it leads
def ct.lead(+ss: String, +qq: String, +rr: String) -> ct.has((ss ++ qq) ++ rr, ss):
  e1 = Equal.sym(String, (ss ++ qq) ++ rr, ss ++ (qq ++ rr), ct.assoc(ss, qq, rr))
  %e1 : {String.contains(_, ss) == True{} : Bool}
  ct.front(ss, qq ++ rr)

# the type that is empty exactly where a Maybe is Some
def mb.emp(mm: Maybe<&2, String>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_s}:
      Empty

# that None is Some
def mb.none_some(ss: String) -> Type:
  {None{} == Some{ss} : Maybe<&2, String>}

# None is not Some
def mb.clash(+ss: String, eq: mb.none_some(ss)) -> Empty:
  %eq : mb.emp(_)
  Unit{}

# an error with no suggestion proves anything about its text
def tp.none(
  +spec: S.Cli,
  +err: S.ParseErr,
  +ss: String,
  eq: mb.none_some(ss)
) -> ct.has(S.err_text(spec, err), ss):
  Empty.absurd(ct.has(S.err_text(spec, err), ss), mb.clash(ss, eq))

def Laws.err_text_tip(spec, err, ss, h_sug):
  match err:
    case S.UnknownFlag{+at, +word}:
      e1 = Equal.sym(Maybe<&2, String>, S.sug.word(spec, at, word), Some{ss}, h_sug)
      %e1 : {String.contains(S.err.wrap(spec, at, "error: unexpected argument '" ++ word ++ "' found" ++ S.sug.tip(_)),
        ss) == True{} : Bool}
      ct.step("error: unexpected argument '",
          word ++ "' found" ++ "\n\n  tip: a similar argument exists: '" ++ ss ++ "'",
        "\n\n" ++ S.usage.at(spec, at) ++ "\n\n" ++ S.err.hint(at), ss,
        ct.step(word, "' found" ++ "\n\n  tip: a similar argument exists: '" ++ ss ++ "'",
          "\n\n" ++ S.usage.at(spec, at) ++ "\n\n" ++ S.err.hint(at), ss,
          ct.step("' found", "\n\n  tip: a similar argument exists: '" ++ ss ++ "'",
            "\n\n" ++ S.usage.at(spec, at) ++ "\n\n" ++ S.err.hint(at), ss,
            ct.step("\n\n  tip: a similar argument exists: '", ss ++ "'",
              "\n\n" ++ S.usage.at(spec, at) ++ "\n\n" ++ S.err.hint(at), ss,
              ct.lead(ss, "'", "\n\n" ++ S.usage.at(spec, at) ++ "\n\n" ++ S.err.hint(at))))))
    case S.Missing{+at, +name}:
      tp.none(spec, S.Missing{at, name}, ss, h_sug)
    case S.NoValue{+at, +name}:
      tp.none(spec, S.NoValue{at, name}, ss, h_sug)
    case S.BadValue{+at, +name, +value}:
      tp.none(spec, S.BadValue{at, name, value}, ss, h_sug)
    case S.NeedHelp{+path}:
      tp.none(spec, S.NeedHelp{path}, ss, h_sug)
    case S.Unexpected{+at, +arg}:
      tp.none(spec, S.Unexpected{at, arg}, ss, h_sug)
    case S.Repeated{+at, +name}:
      tp.none(spec, S.Repeated{at, name}, ss, h_sug)
    case S.NeedVersion{}:
      tp.none(spec, S.NeedVersion{}, ss, h_sug)
