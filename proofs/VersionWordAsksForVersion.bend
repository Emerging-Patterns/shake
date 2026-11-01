# proofs of laws/VersionWordAsksForVersion.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/VersionWordAsksForVersion.bend as Laws

# the code's version check is the law's
def va.asks(
  spec: Shake.Cli,
  +at: List<&2, String>,
  +word: String
) -> {S.version.asks(spec, at, word) == Laws.asks_version(spec, at, word) : Bool}:
  match spec:
    case S.Cli{_n, _a, _v, _g, _s}:
      {==}

# the parse is the walk's answer, read for the version
def va.res(
  +spec: Shake.Cli,
  +ws: List<&2, String>,
  +rr: Result<&2, &2, S.ParseErr, S.Matched>,
  h_walk: {S.parse.finish(S.parse.walk(ws, S.parse.start(spec))) == rr : Result<&2, &2, S.ParseErr, S.Matched>}
) -> {Shake.parse(spec, ws) == S.version.res(spec, rr) : Result<&2, &2, S.ParseErr, S.Matched>}:
  Equal.cong(Result<&2, &2, S.ParseErr, S.Matched>, Result<&2, &2, S.ParseErr, S.Matched>,
    xx => S.version.res(spec, xx), S.parse.finish(S.parse.walk(ws, S.parse.start(spec))), rr, h_walk)

# a refused word read for the version, its check answered
def va.pick(
  +spec: Shake.Cli,
  +at: List<&2, String>,
  +word: String,
  +bb: Bool,
  h_asks: {Laws.asks_version(spec, at, word) == bb : Bool}
) -> {S.version.res(spec, Fail{S.UnknownFlag{at, word}})
    == Fail{Bool.pick(S.ParseErr, bb, S.NeedVersion{}, S.UnknownFlag{at, word})}
    : Result<&2, &2, S.ParseErr, S.Matched>}:
  ee = Equal.trans(Bool, S.version.asks(spec, at, word), Laws.asks_version(spec, at, word), bb, va.asks(spec, at, word),
    h_asks)
  Equal.cong(Bool, Result<&2, &2, S.ParseErr, S.Matched>,
    xx => Fail{Bool.pick(S.ParseErr, xx, S.NeedVersion{}, S.UnknownFlag{at, word})}, S.version.asks(spec, at, word), bb,
    ee)

def Laws.version_asked(spec, ws, at, word, h_walk, h_asks):
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, ws),
    S.version.res(spec, Fail{S.UnknownFlag{at, word}}), Fail{S.NeedVersion{}},
    va.res(spec, ws, Fail{S.UnknownFlag{at, word}}, h_walk), va.pick(spec, at, word, True{}, h_asks))

def Laws.version_unasked(spec, ws, at, word, h_walk, h_asks):
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, ws),
    S.version.res(spec, Fail{S.UnknownFlag{at, word}}), Fail{S.UnknownFlag{at, word}},
    va.res(spec, ws, Fail{S.UnknownFlag{at, word}}, h_walk), va.pick(spec, at, word, False{}, h_asks))

# an answer that refuses no unknown option is left as it is
def va.other(
  +spec: Shake.Cli,
  rr: Result<&2, &2, S.ParseErr, S.Matched>,
  h_rr: {Laws.unknown.res(rr) == False{} : Bool}
) -> {S.version.res(spec, rr) == rr : Result<&2, &2, S.ParseErr, S.Matched>}:
  match rr:
    case Done{_m}:
      {==}
    case Fail{ee}:
      match ee:
        case S.UnknownFlag{at, word}:
          Empty.absurd({S.version.res(spec, Fail{S.UnknownFlag{at, word}}) == Fail{S.UnknownFlag{at, word}}
            : Result<&2, &2, S.ParseErr, S.Matched>}, Walk.wk.true_false(h_rr))
        case S.Missing{_at, _name}:
          {==}
        case S.NoValue{_at, _name}:
          {==}
        case S.BadValue{_at, _name, _value}:
          {==}
        case S.NeedHelp{_path}:
          {==}
        case S.Unexpected{_at, _arg}:
          {==}
        case S.Repeated{_at, _name}:
          {==}
        case S.NeedVersion{}:
          {==}

def Laws.version_other(spec, ws, rr, h_walk, h_rr):
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>, Shake.parse(spec, ws), S.version.res(spec, rr), rr,
    va.res(spec, ws, rr, h_walk), va.other(spec, rr, h_rr))

# a lookup's answer, read as absent or not, under one answer of the check
def rl.at(
  bb: Bool,
  +x1: S.Arg,
  +x2: S.Arg,
  +r1: Maybe<&2, S.Arg>,
  +r2: Maybe<&2, S.Arg>,
  e: {Maybe.is_none(&2, S.Arg, r1) == Maybe.is_none(&2, S.Arg, r2) : Bool}
) -> {Maybe.is_none(&2, S.Arg, S.by_long.at(bb, x1, r1)) == Maybe.is_none(&2, S.Arg, S.by_long.at(bb, x2, r2))
    : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      e

# resolved arguments spell long what they spelled
def rl.none(
  args: List<&2, S.Arg>,
  +vars: List<&2, Shake.Var>,
  +name: String
) -> {Maybe.is_none(&2, S.Arg, S.by_long(S.resolve.args(args, vars), name))
    == Maybe.is_none(&2, S.Arg, S.by_long(args, name)) : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Arg{+n, +s, +l, +k, +h, +r, fb, +cs}:
          match fb:
            case S.Fallback{+ev, +dd}:
              +orig = {S.Arg{n, s, l, k, h, r, S.Fallback{ev, dd}, cs} : S.Arg}
              rl.at(S.by_long.hit(orig, name), S.resolve.arg(orig, vars), orig,
                S.by_long(S.resolve.args(tt, vars), name), S.by_long(tt, name), rl.none(tt, vars, name))

def Laws.resolve_asks(spec, vars, at, word):
  match spec:
    case S.Cli{+nn, +ab, +vv, +gg, +ss}:
      Equal.cong(Bool, Bool, xx => Bool.and(Bool.or(String.eq(word, "--version"), Bool.and(String.eq(word, "-V"), xx)),
          Bool.and(List.is_empty(&2, String, at), Maybe.is_some(&2, String, vv))),
        Maybe.is_none(&2, S.Arg, S.by_long(S.resolve.args(gg, vars), "version")),
        Maybe.is_none(&2, S.Arg, S.by_long(gg, "version")), rl.none(gg, vars, "version"))
