# proofs of laws/CheckReportsSpecErrors.bend
import Base
import ../src/cli.bend as S
import ../src/check.bend as K
import ../laws/CheckReportsSpecErrors.bend as Laws
import ../laws/defs/ArgumentLists.bend as D1
import ./lemmas/NameAppend.bend as M1

# two report lists, each equal to another, one after the other
def sc.both(
  +x1: List<&2, K.SpecErr>,
  +y1: List<&2, K.SpecErr>,
  +x2: List<&2, K.SpecErr>,
  +y2: List<&2, K.SpecErr>,
  e1: {x1 == y1 : List<&2, K.SpecErr>},
  e2: {x2 == y2 : List<&2, K.SpecErr>}
) -> {K.both(x1, x2) == K.both(y1, y2) : List<&2, K.SpecErr>}:
  Equal.trans(List<&2, K.SpecErr>, K.both(x1, x2), K.both(y1, x2), K.both(y1, y2),
    Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>, zz => K.both(zz, x2), x1, y1, e1),
    Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>, zz => K.both(y1, zz), x2, y2, e2))

# a listed-or-not answer, then the rest's
def sc.ok.at(
  bb: Bool,
  +r1: Bool,
  +r2: Bool,
  ee: {r1 == r2 : Bool}
) -> {S.allowed.ok.at(bb, r1) == List.any.if(_u => r2, bb) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ee

# a value is listed among choices when the choices contain it
def sc.ok(
  cs: List<&2, String>,
  +vv: String
) -> {S.allowed.ok(cs, vv) == List.contains(~String, ~String.eq, cs, vv) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      sc.ok.at(String.eq(hh, vv), S.allowed.ok(tt, vv), List.contains(~String, ~String.eq, tt, vv), sc.ok(tt, vv))

# the default's report is the one the law names
def sc.dflt(
  +path: List<&2, String>,
  +name: String,
  +cs: List<&2, String>,
  dflt: Maybe<&2, String>
) -> {K.args.default(dflt, cs, path, name) == D1.off_choice(path, name, cs, dflt) : List<&2, K.SpecErr>}:
  match dflt:
    case None{}:
      {==}
    case Some{+vv}:
      Equal.cong(Bool, List<&2, K.SpecErr>,
        bb => K.one(Bool.and(Bool.not(List.is_empty(&2, String, cs)), Bool.not(bb)),
          K.DefaultNotChoice{path, name, vv}),
        S.allowed.ok(cs, vv), List.contains(~String, ~String.eq, cs, vv), sc.ok(cs, vv))

# the argument reports, from the arguments before
def sc.args(
  args: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> {K.args.dups(args, path, D1.arg_names(before), D1.arg_shorts(before), D1.arg_longs(before))
    == D1.args_reports(args, path, before) : List<&2, K.SpecErr>}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+name, +short, +long, +kind, +help, +req, S.Fallback{+ev, +dflt}, +cs}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(
              K.one(List.contains(~String, ~String.eq, D1.arg_names(before), name), K.SameName{path, name}),
              K.both(K.one(K.spelled.seen(short, D1.arg_shorts(before)), K.SameShort{path, S.text.of(short, "")}),
                K.both(K.one(K.spelled.seen(long, D1.arg_longs(before)), K.SameLong{path, S.text.of(long, "")}),
                  zz))),
            K.both(K.args.default(dflt, cs, path, name),
              K.args.dups(tt, path, name <> D1.arg_names(before), K.spelled.add(short, D1.arg_shorts(before)),
                K.spelled.add(long, D1.arg_longs(before)))),
            K.both(D1.off_choice(path, name, cs, dflt),
              D1.args_reports(tt, path, S.Arg{name, short, long, kind, help, req, S.Fallback{ev, dflt},
                  cs} <> before)),
            sc.both(K.args.default(dflt, cs, path, name), D1.off_choice(path, name, cs, dflt),
              K.args.dups(tt, path, name <> D1.arg_names(before), K.spelled.add(short, D1.arg_shorts(before)),
                K.spelled.add(long, D1.arg_longs(before))),
              D1.args_reports(tt, path, S.Arg{name, short, long, kind, help, req, S.Fallback{ev, dflt},
                  cs} <> before),
              sc.dflt(path, name, cs, dflt),
              sc.args(tt, path, S.Arg{name, short, long, kind, help, req, S.Fallback{ev, dflt}, cs} <> before)))

# the positional reports, from the positionals before
def sc.pos(
  pos: List<&2, S.Arg>,
  +path: List<&2, String>,
  +before: List<&2, S.Arg>
) -> {K.pos.order(pos, path, D1.any_optional(before)) == D1.pos_reports(pos, path, before)
    : List<&2, K.SpecErr>}:
  match pos:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+name, +short, +long, +kind, +help, +req, +dflt, +cs}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(
              K.one(Bool.and(S.rest.is.kind(kind), Bool.not(List.is_empty(&2, S.Arg, tt))), K.RestNotLast{path, name}),
              K.both(K.one(Bool.and(req, D1.any_optional(before)), K.RequiredAfterOptional{path, name}), zz)),
            K.pos.order(tt, path, Bool.or(D1.any_optional(before), Bool.not(req))),
            D1.pos_reports(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before),
            sc.pos(tt, path, S.Arg{name, short, long, kind, help, req, dflt, cs} <> before))

# the subcommand reports, from the subcommands before
def sc.subs(
  subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +before: List<&2, S.Sub>
) -> {K.subs.dups(subs, path, D1.sub_names(before)) == D1.sub_reports(subs, path, before) : List<&2, K.SpecErr>}:
  match subs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Sub{+name, +about, +args, +kids}:
          Equal.cong(List<&2, K.SpecErr>, List<&2, K.SpecErr>,
            zz => K.both(K.one(List.contains(~String, ~String.eq, D1.sub_names(before), name), K.SameSub{path, name}),
              K.both(K.one(String.eq(name, "help"), K.HelpSub{path}), zz)),
            K.subs.dups(tt, path, name <> D1.sub_names(before)),
            D1.sub_reports(tt, path, S.Sub{name, about, args, kids} <> before),
            sc.subs(tt, path, S.Sub{name, about, args, kids} <> before))

# one command's reports
def sc.cmd(
  +path: List<&2, String>,
  +args: List<&2, S.Arg>,
  +subs: List<&2, S.Sub>
) -> {K.cmd(path, args, subs) == D1.cmd_reports(path, args, subs) : List<&2, K.SpecErr>}:
  sc.both(K.args.dups(args, path, [], [], []), D1.args_reports(args, path, []),
    K.both(K.pos.order(S.pos_of(args), path, False{}), K.subs.dups(subs, path, [])),
    K.both(D1.pos_reports(S.pos_of(args), path, []), D1.sub_reports(subs, path, [])),
    sc.args(args, path, []),
    sc.both(K.pos.order(S.pos_of(args), path, False{}), D1.pos_reports(S.pos_of(args), path, []),
      K.subs.dups(subs, path, []), D1.sub_reports(subs, path, []),
      sc.pos(S.pos_of(args), path, []), sc.subs(subs, path, [])))

# reversing names onto a list is reversing them, then appending it
def sc.rev_go(
  xs: List<&2, String>,
  +acc: List<&2, String>
) -> {List.reverse.go(&2, String, xs, acc) == List.append(&2, String, List.reverse.go(&2, String, xs, []), acc)
    : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, tt, hh <> acc),
        List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
        List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
        sc.rev_go(tt, hh <> acc),
        Equal.sym(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
          List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
          Equal.trans(List<&2, String>,
            List.append(&2, String, List.reverse.go(&2, String, tt, [hh]), acc),
            List.append(&2, String, List.append(&2, String, List.reverse.go(&2, String, tt, []), [hh]), acc),
            List.append(&2, String, List.reverse.go(&2, String, tt, []), hh <> acc),
            Equal.cong(List<&2, String>, List<&2, String>, ys => List.append(&2, String, ys, acc),
              List.reverse.go(&2, String, tt, [hh]),
              List.append(&2, String, List.reverse.go(&2, String, tt, []), [hh]), sc.rev_go(tt, [hh])),
            M1.sc.app(List.reverse.go(&2, String, tt, []), [hh], acc))))

# a reversed path with a name in front is the path, then the name
def sc.rev(
  +name: String,
  back: List<&2, String>
) -> {List.reverse(&2, String, name <> back) == List.append(&2, String, List.reverse(&2, String, back), [name])
    : List<&2, String>}:
  sc.rev_go(back, [name])

# every subcommand's reports, under a reversed path
def sc.forest(
  subs: List<&2, S.Sub>,
  +back: List<&2, String>
) -> {K.forest(subs, back) == D1.below(subs, List.reverse(&2, String, back)) : List<&2, K.SpecErr>}:
  match subs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Sub{+name, _a, +args, +kids}:
          +rn = List.reverse(&2, String, name <> back)
          +rp = List.append(&2, String, List.reverse(&2, String, back), [name])
          sc.both(K.cmd(rn, args, kids), D1.cmd_reports(rp, args, kids),
            K.both(K.forest(kids, name <> back), K.forest(tt, back)),
            K.both(D1.below(kids, rp), D1.below(tt, List.reverse(&2, String, back))),
            Equal.trans(List<&2, K.SpecErr>, K.cmd(rn, args, kids), D1.cmd_reports(rn, args, kids),
              D1.cmd_reports(rp, args, kids), sc.cmd(rn, args, kids),
              Equal.cong(List<&2, String>, List<&2, K.SpecErr>, pp => D1.cmd_reports(pp, args, kids), rn, rp,
                sc.rev(name, back))),
            sc.both(K.forest(kids, name <> back), D1.below(kids, rp), K.forest(tt, back),
              D1.below(tt, List.reverse(&2, String, back)),
              Equal.trans(List<&2, K.SpecErr>, K.forest(kids, name <> back), D1.below(kids, rn),
                D1.below(kids, rp), sc.forest(kids, name <> back),
                Equal.cong(List<&2, String>, List<&2, K.SpecErr>, pp => D1.below(kids, pp), rn, rp,
                  sc.rev(name, back))),
              sc.forest(tt, back)))

def Laws.check_listed(_name, _about, _version, args, subs):
  sc.both(K.cmd([], args, subs), D1.cmd_reports([], args, subs), K.forest(subs, []), D1.below(subs, []),
    sc.cmd([], args, subs), sc.forest(subs, []))
