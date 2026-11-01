# the help walk over the words after a request for help
import Base
import ../../main.bend as Shake
import ../../src/cli.bend as S
import ../../src/walk.bend as Walk
import ../../src/grow.bend as Grow
import ../../laws/HelpWalk.bend as L1
import ../../laws/defs/HelpPathNames.bend as D1
import ./WalkSteps.bend as M1

# the first word of a list, or none
def hp.head(ns: List<&2, String>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{hh, _t}:
      hh

# what `hp.walk` claims
def hp.ty(
  +ns: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool
) -> Type:
  &kids: List<&2, S.Sub> -> {S.parse.walk(ns, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen})
    == S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen} : S.St}

# the names under a found subcommand, carried to its own subcommands
def hp.names_tr(
  +tt: List<&2, String>,
  +aa: List<&2, S.Sub>,
  +bb: List<&2, S.Sub>,
  ee: {aa == bb : List<&2, S.Sub>},
  hh: {D1.help_names(tt, aa) == True{} : Bool}
) -> {D1.help_names(tt, bb) == True{} : Bool}:
  Equal.trans(Bool, D1.help_names(tt, bb), D1.help_names(tt, aa), True{},
    Equal.cong(List<&2, S.Sub>, Bool, kk => D1.help_names(tt, kk), bb, aa, Equal.sym(List<&2, S.Sub>, aa, bb,
        ee)), hh)

# one name further down the help path, then the rest
def hp.cons(
  +nn: String,
  +tt: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +sn: String,
  +sa: String,
  +sg: List<&2, S.Arg>,
  +kids: List<&2, S.Sub>,
  e_fm: {S.find_sub(subs, nn) == Some{S.Sub{sn, sa, sg, kids}} : Maybe<&2, S.Sub>},
  ih: hp.ty(tt, args, up, kids, List.append(&2, String, path, [nn]), bs, pos, raw, seen)
) -> hp.ty(nn <> tt, args, up, subs, path, bs, pos, raw, seen):
  (k2, e2) = ih
  +k3 = {k2 : List<&2, S.Sub>}
  +mid = {S.St{S.Help{}, args, up, kids, List.append(&2, String, path, [nn]), bs, pos, raw, seen} : S.St}
  +fin_st = {S.St{S.Help{}, args, up, k3, List.append(&2, String, path, nn <> tt), bs, pos, raw, seen} : S.St}
  es = Equal.cong(Maybe<&2, S.Sub>, S.St, mm => S.parse.walk(tt, S.parse.step.help_path(mm, nn, args, up, subs,
      path, bs,
      pos, raw, seen)), S.find_sub(subs, nn), Some{S.Sub{sn, sa, sg, kids}}, e_fm)
  (k3, Equal.trans(S.St, S.parse.walk(nn <> tt, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen}),
    S.parse.walk(tt, mid), fin_st, es,
    Equal.trans(S.St, S.parse.walk(tt, mid),
      S.St{S.Help{}, args, up, k3, List.append(&2, String, List.append(&2, String, path, [nn]), tt), bs, pos,
          raw, seen},
      fin_st, e2,
      Equal.cong(List<&2, String>, S.St, pp => S.St{S.Help{}, args, up, k3, pp, bs, pos, raw, seen},
        List.append(&2, String, List.append(&2, String, path, [nn]), tt), List.append(&2, String, path, nn <> tt),
        Grow.gw.sapp(path, [nn], tt)))))

# words that each name a subcommand under the one before extend a help path
def hp.walk(
  ns: List<&2, String>,
  +subs: List<&2, S.Sub>,
  fm: Maybe<&2, S.Sub>,
  +e_fm: {S.find_sub(subs, hp.head(ns)) == fm : Maybe<&2, S.Sub>},
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +h_ns: {D1.help_names(ns, subs) == True{} : Bool}
) -> hp.ty(ns, args, up, subs, path, bs, pos, raw, seen):
  match ns:
    case Nil{}:
      (subs, Equal.cong(List<&2, String>, S.St, pp => S.St{S.Help{}, args, up, subs, pp, bs, pos, raw, seen}, path,
        List.append(&2, String, path, []), Equal.sym(List<&2, String>, List.append(&2, String, path, []), path,
          Grow.gw.nil_s(path))))
    case Con{+nn, +tt}:
      match fm:
        case None{}:
          Empty.absurd(hp.ty(nn <> tt, args, up, subs, path, bs, pos, raw, seen),
            Walk.wk.false_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)), True{},
              Equal.cong(Maybe<&2, S.Sub>, Bool, mm => Maybe.is_some(&2, S.Sub, mm), None{}, S.find_sub(subs, nn),
                Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, nn), None{}, e_fm)),
              Walk.wk.and_l(Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)),
                D1.help_names(tt, D1.kids_of(S.find_sub(subs, nn))), h_ns))))
        case Some{ss}:
          match ss:
            case S.Sub{+sn, +sa, +sg, +kids}:
              hp.cons(nn, tt, args, up, subs, path, bs, pos, raw, seen, sn, sa, sg, kids, e_fm,
                hp.walk(tt, kids, S.find_sub(kids, hp.head(tt)), {==}, args, up, List.append(&2, String, path,
                    [nn]), bs,
                  pos, raw, seen,
                  hp.names_tr(tt, D1.kids_of(S.find_sub(subs, nn)), kids,
                    Equal.cong(Maybe<&2, S.Sub>, List<&2, S.Sub>, mm => D1.kids_of(mm), S.find_sub(subs, nn),
                      Some{S.Sub{sn, sa, sg, kids}}, e_fm),
                    Walk.wk.and_r(Maybe.is_some(&2, S.Sub, S.find_sub(subs, nn)),
                      D1.help_names(tt, D1.kids_of(S.find_sub(subs, nn))), h_ns))))

# the walk after the words before, read from where they left the walker
def hp.from(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +ns: List<&2, String>,
  +st: S.St,
  +big: S.St,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == st : S.St},
  ew: {S.parse.walk(ns, st) == big : S.St}
) -> {S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec)) == big : S.St}:
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec)), S.parse.walk(ns, st), big,
    M1.rest.after(spec, pre, ns, st, h_at), ew)

# the help walk, read from the start
def hp.at(
  +spec: Shake.Cli,
  +pre: List<&2, String>,
  +ns: List<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_at: {S.parse.walk(pre, S.parse.start(spec)) == S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen} : S.St},
  ww: hp.ty(ns, args, up, subs, path, bs, pos, raw, seen)
) -> &kids: List<&2, S.Sub> -> {S.parse.walk(List.append(&2, String, pre, ns), S.parse.start(spec))
    == S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen} : S.St}:
  (k1, e1) = ww
  +kids = {k1 : List<&2, S.Sub>}
  (kids, hp.from(spec, pre, ns, S.St{S.Help{}, args, up, subs, path, bs, pos, raw, seen},
    S.St{S.Help{}, args, up, kids, List.append(&2, String, path, ns), bs, pos, raw, seen}, h_at, e1))

def L1.help_walk(spec, pre, ns, args, up, subs, path, bs, pos, raw, seen, h_at, h_ns):
  hp.at(spec, pre, ns, args, up, subs, path, bs, pos, raw, seen, h_at,
    hp.walk(ns, subs, S.find_sub(subs, hp.head(ns)), {==}, args, up, path, bs, pos, raw, seen, h_ns))
