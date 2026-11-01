# proofs of laws/LongNoName.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/walk.bend as Walk
import ../laws/DropZero.bend as L1
import ../laws/LongNoName.bend as Laws
import ../laws/PrefixEmpty.bend as L2
import ../laws/Refused.bend as L3
import ../laws/defs/WalkerFailure.bend as D1
import ./lemmas/FailedWalkThrough.bend as M1
import ./lemmas/WalkSteps.bend as M2

# `--=...` fails the step
def long_no_name.step(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +seen: Bool,
  h_dd: {String.eq("--" ++ body, "--") == False{} : Bool},
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_empty: {String.is_empty(name) == True{} : Bool}
) -> {D1.dead_of(S.parse.step("--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen}))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}:
  e1 = Equal.sym(Bool, String.eq("--" ++ body, "--"), False{}, h_dd)
  %e1 : {D1.dead_of(S.parse.step.end(_, "--" ++ body, args, up, subs, path, bs, pos, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e0 = Equal.sym(Bool, String.starts_with(body, ""), True{}, L2.prefix_empty(body))
  %e0 : {D1.dead_of(S.parse.step.kind.go(_, True{}, "--" ++ body, args, up, subs, path, bs, pos, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  ed = Equal.sym(String, String.drop(body, 0n), body, L1.drop_zero(body))
  %ed : {D1.dead_of(S.parse.take_long(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e2 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e2 : {D1.dead_of(S.parse.take_long.cut(_, "--" ++ body, args, up, subs, path, bs, pos, False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  e3 = Equal.sym(Bool, String.is_empty(name), True{}, h_empty)
  %e3 : {D1.dead_of(S.parse.take_long.named(_, name, val, "--" ++ body, args, up, subs, path, bs, pos,
      False{}, seen))
    == Some{S.UnknownFlag{path, "--" ++ body}} : Maybe<&2, S.ParseErr>}
  {==}

# a word `--=...` read as `--version` would cut to the name `version`, not
# to no name
def lnv.clash(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  +h_empty: {String.is_empty(name) == True{} : Bool},
  e: {String.eq("--" ++ body, "--version") == True{} : Bool}
) -> Empty:
  ew = Eq.string_eq_true("--" ++ body, "--version", e)
  eb = Equal.trans(String, body, String.drop(body, 0n), "version",
    Equal.sym(String, String.drop(body, 0n), body, L1.drop_zero(body)),
    Equal.cong(String, String, ss => String.drop(ss, 2n), "--" ++ body, "--version", ew))
  ec = Equal.trans(String & Maybe<&2, String>, (name, val), S.cut_eq(body), S.cut_eq("version"),
    Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut),
    Equal.cong(String, String & Maybe<&2, String>, ss => S.cut_eq(ss), body, "version", eb))
  en = Equal.cong(String & Maybe<&2, String>, Bool, cv => String.is_empty(Pair.fst(String, Maybe<&2, String>, cv)),
    (name, val), S.cut_eq("version"), ec)
  Walk.wk.true_false(Equal.trans(Bool, True{}, String.is_empty(name), False{},
    Equal.sym(Bool, String.is_empty(name), True{}, h_empty), en))

# the same, as an answer told apart by cases
def lnv.go(
  bb: Bool,
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  +h_empty: {String.is_empty(name) == True{} : Bool},
  e: {String.eq("--" ++ body, "--version") == bb : Bool}
) -> {String.eq("--" ++ body, "--version") == False{} : Bool}:
  match bb:
    case False{}:
      e
    case True{}:
      Empty.absurd({String.eq("--" ++ body, "--version") == False{} : Bool},
        lnv.clash(body, name, val, h_cut, h_empty, e))

# a word `--=...` is not `--version`
def lnv.word(
  +body: String,
  +name: String,
  +val: Maybe<&2, String>,
  +h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  +h_empty: {String.is_empty(name) == True{} : Bool}
) -> {String.eq("--" ++ body, "--version") == False{} : Bool}:
  lnv.go(String.eq("--" ++ body, "--version"), body, name, val, h_cut, h_empty, {==})

# so it asks for no version
def lnv.asks(
  +spec: Shake.Cli,
  +path: List<&2, String>,
  +body: String,
  name: String,
  val: Maybe<&2, String>,
  h_cut: {S.cut_eq(body) == (name, val) : String & Maybe<&2, String>},
  h_empty: {String.is_empty(name) == True{} : Bool}
) -> {S.version.asks(spec, path, "--" ++ body) == False{} : Bool}:
  match spec:
    case S.Cli{+nn, +aa, +vv, +gg, +ss}:
      ee = Equal.sym(Bool, String.eq("--" ++ body, "--version"), False{}, lnv.word(body, name, val, h_cut, h_empty))
      %ee : {Bool.and(Bool.or(_, Bool.and(String.eq("--" ++ body, "-V"),
          Maybe.is_none(&2, S.Arg, S.by_long(gg, "version")))),
        Bool.and(List.is_empty(&2, String, path), Maybe.is_some(&2, String, vv))) == False{} : Bool}
      el = Equal.sym(Cmp, String.order.go(body, "", LT{}), LT{}, Eq.string_order_lt(body, ""))
      %el : {Bool.and(Bool.and(Cmp.is_eq(_), Bool.not(Maybe.is_some(&2, S.Arg, S.by_long(gg, "version")))),
        Bool.and(List.is_empty(&2, String, path), Maybe.is_some(&2, String, vv))) == False{} : Bool}
      {==}

def Laws.long_no_name(
  spec,
  pre,
  more,
  body,
  name,
  val,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  h_at,
  h_dd,
  h_cut,
  h_empty
):
  +er = {S.UnknownFlag{path, "--" ++ body} : S.ParseErr}
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>,
    Shake.parse(spec, List.append(&2, String, List.append(&2, String, pre, ["--" ++ body]), more)),
    Fail{S.version.err(spec, er)}, Fail{er},
    L3.refused(spec, pre, more, "--" ++ body, S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen},
        er, h_at,
      long_no_name.step(body, name, val, args, up, subs, path, bs, pos, seen, h_dd, h_cut, h_empty)),
    M1.fs.keep(spec, path, "--" ++ body, lnv.asks(spec, path, body, name, val, h_cut, h_empty)))
