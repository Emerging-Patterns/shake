# proofs of laws/EnvFallsBetweenWordsAndDefault.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/EnvFallsBetweenWordsAndDefault.bend as Laws
import ../laws/EnvValueOutsideChoicesFails.bend as L1
import ./lemmas/EnvChecksNoArgs.bend as M1

def Laws.env_sets(_nn, _sh, _lo, _kind, _hp, _req, _ev, _dd, _cs, _var):
  {==}

def Laws.env_of_none(_vars):
  {==}

def Laws.env_of_nil(_var):
  {==}

def Laws.env_of_hit(var, nn, vv, rest, h_eq, h_full):
  e1 = Equal.sym(Bool, String.eq(nn, var), True{}, h_eq)
  %e1 : {S.env.full(S.env.get.at(_, vv, S.env.get(rest, var))) == Some{vv} : Maybe<&2, String>}
  e2 = Equal.sym(Bool, String.is_empty(vv), False{}, h_full)
  %e2 : {Bool.pick(Maybe<&2, String>, _, None{}, Some{vv}) == Some{vv} : Maybe<&2, String>}
  {==}

def Laws.env_of_empty(var, nn, vv, rest, h_eq, h_empty):
  e1 = Equal.sym(Bool, String.eq(nn, var), True{}, h_eq)
  %e1 : {S.env.full(S.env.get.at(_, vv, S.env.get(rest, var))) == None{} : Maybe<&2, String>}
  e2 = Equal.sym(Bool, String.is_empty(vv), True{}, h_empty)
  %e2 : {Bool.pick(Maybe<&2, String>, _, None{}, Some{vv}) == None{} : Maybe<&2, String>}
  {==}

def Laws.env_of_skip(var, nn, vv, rest, h_eq):
  e1 = Equal.sym(Bool, String.eq(nn, var), False{}, h_eq)
  %e1 : {S.env.full(S.env.get.at(_, vv, S.env.get(rest, var))) == S.env.of(Some{var}, rest)
    : Maybe<&2, String>}
  {==}

# that a kind is not a flag
def fb.not_flag(kk: S.ArgKind) -> Type:
  {S.env.flag.is(kk) == False{} : Bool}

# what an env value gives an argument other than a flag is that value
def fb.kind(
  kk: S.ArgKind,
  +vv: String,
  hh: fb.not_flag(kk)
) -> {S.env.kind(kk, vv) == Some{vv} : Maybe<&2, String>}:
  match kk:
    case S.Flag{}:
      Empty.absurd({S.env.kind(S.Flag{}, vv) == Some{vv} : Maybe<&2, String>}, Walk.wk.true_false(hh))
    case S.Opt{}:
      {==}
    case S.Many{}:
      {==}
    case S.Pos{}:
      {==}
    case S.Rest{}:
      {==}

def Laws.fallback_env(nn, sh, lo, kind, hp, req, ev, dd, cs, vars, vv, h_kind, h_env):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.Arg{nn, sh, lo, kind, hp, req, S.resolve.with(_, kind, ev, dd), cs}
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{vv}}, cs} : S.Arg}
  e2 = Equal.sym(Maybe<&2, String>, S.env.kind(kind, vv), Some{vv}, fb.kind(kind, vv, h_kind))
  %e2 : {S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, _}, cs}
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{vv}}, cs} : S.Arg}
  {==}

def Laws.fallback_flag_on(nn, sh, lo, hp, req, ev, dd, cs, vars, vv, h_env, h_on):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.resolve.with(_, S.Flag{}, ev, dd), cs}
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, Some{"true"}}, cs} : S.Arg}
  e2 = Equal.sym(Bool, S.allowed.ok(Laws.off_words(), String.to_lower(vv)), False{}, h_on)
  %e2 : {S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, Bool.pick(Maybe<&2, String>, _, None{}, Some{"true"})}, cs}
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, Some{"true"}}, cs} : S.Arg}
  {==}

def Laws.fallback_flag_off(nn, sh, lo, hp, req, ev, dd, cs, vars, vv, h_env, h_off):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.resolve.with(_, S.Flag{}, ev, dd), cs}
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, None{}}, cs} : S.Arg}
  e2 = Equal.sym(Bool, S.allowed.ok(Laws.off_words(), String.to_lower(vv)), True{}, h_off)
  %e2 : {S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, Bool.pick(Maybe<&2, String>, _, None{}, Some{"true"})}, cs}
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, None{}}, cs} : S.Arg}
  {==}

def Laws.fallback_default(nn, sh, lo, kind, hp, req, ev, dd, cs, vars, h_env):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), None{}, h_env)
  %e1 : {S.Arg{nn, sh, lo, kind, hp, req, S.resolve.with(_, kind, ev, dd), cs}
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs} : S.Arg}
  {==}

def Laws.resolve_spec(_nn, _ab, _ver, _args, _subs, _vars):
  {==}

def Laws.resolve_args_con(_aa, _tt, _vars):
  {==}

def Laws.resolve_subs_con(_nn, _ab, _args, _kids, _tt, _vars):
  {==}

def Laws.env_parse(_spec, _ws, _vars):
  {==}

# an argument resolved under no pairs is unchanged
def rs.arg_nil(aa: S.Arg) -> {S.resolve.arg(aa, []) == aa : S.Arg}:
  match aa:
    case S.Arg{+n, +s, +l, +kk, +h, +r, fb, +cs}:
      match fb:
        case S.Fallback{ev, +dd}:
          match ev:
            case None{}:
              {==}
            case Some{+var}:
              {==}

# arguments resolved under no pairs are unchanged
def rs.args_nil(args: List<&2, S.Arg>) -> {S.resolve.args(args, []) == args : List<&2, S.Arg>}:
  match args:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      e1 = Equal.sym(S.Arg, S.resolve.arg(hh, []), hh, rs.arg_nil(hh))
      %e1 : {_ <> S.resolve.args(tt, []) == hh <> tt : List<&2, S.Arg>}
      e2 = Equal.sym(List<&2, S.Arg>, S.resolve.args(tt, []), tt, rs.args_nil(tt))
      %e2 : {hh <> _ == hh <> tt : List<&2, S.Arg>}
      {==}

# subcommands resolved under no pairs are unchanged
def rs.subs_nil(subs: List<&2, S.Sub>) -> {S.resolve.subs(subs, []) == subs : List<&2, S.Sub>}:
  match subs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Sub{+n, +a, +args, +kids}:
          e1 = Equal.sym(List<&2, S.Arg>, S.resolve.args(args, []), args, rs.args_nil(args))
          %e1 : {S.Sub{n, a, _, S.resolve.subs(kids, [])} <> S.resolve.subs(tt, [])
            == S.Sub{n, a, args, kids} <> tt : List<&2, S.Sub>}
          e2 = Equal.sym(List<&2, S.Sub>, S.resolve.subs(kids, []), kids, rs.subs_nil(kids))
          %e2 : {S.Sub{n, a, args, _} <> S.resolve.subs(tt, []) == S.Sub{n, a, args, kids} <> tt : List<&2, S.Sub>}
          e3 = Equal.sym(List<&2, S.Sub>, S.resolve.subs(tt, []), tt, rs.subs_nil(tt))
          %e3 : {S.Sub{n, a, args, kids} <> _ == S.Sub{n, a, args, kids} <> tt : List<&2, S.Sub>}
          {==}

# a spec resolved under no pairs is unchanged
def rs.spec_nil(spec: S.Cli) -> {S.resolve(spec, []) == spec : S.Cli}:
  match spec:
    case S.Cli{+n, +a, +v, +args, +subs}:
      e1 = Equal.sym(List<&2, S.Arg>, S.resolve.args(args, []), args, rs.args_nil(args))
      %e1 : {S.Cli{n, a, v, _, S.resolve.subs(subs, [])} == S.Cli{n, a, v, args, subs} : S.Cli}
      e2 = Equal.sym(List<&2, S.Sub>, S.resolve.subs(subs, []), subs, rs.subs_nil(subs))
      %e2 : {S.Cli{n, a, v, args, _} == S.Cli{n, a, v, args, subs} : S.Cli}
      {==}

# no command on the path has a bad argument under no pairs
def ck.go_nil(
  mm: S.Matched,
  +args: List<&2, S.Arg>,
  +subs: List<&2, S.Sub>
) -> {S.env.bad.go(mm, args, subs, []) == None{} : Maybe<&2, S.Var>}:
  match mm:
    case S.Leaf{+bs}:
      L1.bad_args_nil(args, bs)
    case S.Node{+bs, +name, next}:
      e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.args(args, [], bs), None{}, L1.bad_args_nil(args, bs))
      %e1 : {S.env.first(_,
        S.env.bad.go(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)), []))
        == None{} : Maybe<&2, S.Var>}
      ck.go_nil(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)))

# the check under no pairs leaves every result as it is
def ck.nil(
  spec: S.Cli,
  got: Result<&2, &2, S.ParseErr, S.Matched>
) -> {S.env.check(spec, [], got) == got : Result<&2, &2, S.ParseErr, S.Matched>}:
  match spec:
    case S.Cli{_n, _a, _v, +args, +subs}:
      match got:
        case Fail{_e}:
          {==}
        case Done{+mm}:
          e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.go(mm, args, subs, []), None{}, ck.go_nil(mm, args, subs))
          %e1 : {S.env.check.done(_, mm) == Done{mm} : Result<&2, &2, S.ParseErr, S.Matched>}
          {==}

def Laws.env_none(spec, ws):
  e1 = Equal.sym(S.Cli, S.resolve(spec, []), spec, rs.spec_nil(spec))
  %e1 : {S.env.check(spec, [], S.parse(_, ws)) == S.parse(spec, ws) : Result<&2, &2, S.ParseErr, S.Matched>}
  ck.nil(spec, S.parse(spec, ws))
