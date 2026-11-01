# proofs of laws/EnvValueOutsideChoicesFails.bend
import Base
import ../src/cli.bend as S
import ../laws/EnvValueOutsideChoicesFails.bend as Laws
import ./lemmas/EnvChecksNoArgs.bend as M1

def Laws.env_check_fail(_spec, _vars, _ee):
  {==}

def Laws.env_check_good(_nn, _ab, _ver, args, subs, vars, mm, h_none):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.go(mm, args, subs, vars), None{}, h_none)
  %e1 : {S.env.check.done(_, mm) == Done{mm} : Result<&2, &2, S.ParseErr, S.Matched>}
  {==}

def Laws.env_check_bad(_nn, _ab, _ver, args, subs, vars, mm, name, vv, h_bad):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.go(mm, args, subs, vars), Some{(name, vv)}, h_bad)
  %e1 : {S.env.check.done(_, mm) == Fail{S.BadValue{S.path_of(mm), name, vv}}
    : Result<&2, &2, S.ParseErr, S.Matched>}
  {==}

def Laws.bad_go_leaf(_bs, _args, _subs, _vars):
  {==}

def Laws.bad_go_root(bs, name, next, args, subs, vars, pp, h_here):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.args(args, vars, bs), Some{pp}, h_here)
  %e1 : {S.env.first(_,
    S.env.bad.go(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)), vars))
    == Some{pp} : Maybe<&2, S.Var>}
  {==}

def Laws.bad_go_down(bs, name, next, args, subs, vars, h_none):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.args(args, vars, bs), None{}, h_none)
  %e1 : {S.env.first(_,
    S.env.bad.go(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)), vars))
    == S.env.bad.go(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)), vars)
    : Maybe<&2, S.Var>}
  {==}

def Laws.bad_args_here(aa, tt, vars, bs, pp, h_here):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.arg(aa, vars, bs), Some{pp}, h_here)
  %e1 : {S.env.first(_, S.env.bad.args(tt, vars, bs)) == Some{pp} : Maybe<&2, S.Var>}
  {==}

def Laws.bad_args_next(aa, tt, vars, bs, h_none):
  e1 = Equal.sym(Maybe<&2, S.Var>, S.env.bad.arg(aa, vars, bs), None{}, h_none)
  %e1 : {S.env.first(_, S.env.bad.args(tt, vars, bs)) == S.env.bad.args(tt, vars, bs) : Maybe<&2, S.Var>}
  {==}

# an `and` with a false right side is false
def ba.and_false(bb: Bool) -> {Bool.and(bb, False{}) == False{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a flag is never reported, whatever its env value
def ba.flag(
  found: Maybe<&2, String>,
  +nn: String,
  +cs: List<&2, String>,
  +bs: List<&2, S.Bind>
) -> {S.env.bad.val(found, S.Flag{}, nn, cs, bs) == None{} : Maybe<&2, S.Var>}:
  match found:
    case None{}:
      {==}
    case Some{_vv}:
      {==}

def Laws.bad_arg_some(nn, _sh, _lo, kind, _hp, _req, ev, _dd, cs, vars, bs, vv, h_env, h_kind, h_out, h_bound):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.env.bad.val(_, kind, nn, cs, bs) == Some{(nn, vv)} : Maybe<&2, S.Var>}
  e2 = Equal.sym(Bool, S.env.flag.is(kind), False{}, h_kind)
  %e2 : {Bool.pick(Maybe<&2, S.Var>,
    Bool.and(Bool.not(_), Bool.and(Bool.not(S.allowed(cs, vv)),
      List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv))),
    Some{(nn, vv)}, None{}) == Some{(nn, vv)} : Maybe<&2, S.Var>}
  e3 = Equal.sym(Bool, S.allowed(cs, vv), False{}, h_out)
  %e3 : {Bool.pick(Maybe<&2, S.Var>,
    Bool.and(Bool.not(_), List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv)),
    Some{(nn, vv)}, None{}) == Some{(nn, vv)} : Maybe<&2, S.Var>}
  e4 = Equal.sym(Bool, List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv), True{}, h_bound)
  %e4 : {Bool.pick(Maybe<&2, S.Var>, _, Some{(nn, vv)}, None{}) == Some{(nn, vv)} : Maybe<&2, S.Var>}
  {==}

def Laws.bad_arg_unset(nn, _sh, _lo, kind, _hp, _req, ev, _dd, cs, vars, bs, h_env):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), None{}, h_env)
  %e1 : {S.env.bad.val(_, kind, nn, cs, bs) == None{} : Maybe<&2, S.Var>}
  {==}

def Laws.bad_arg_flag(nn, _sh, _lo, _hp, _req, ev, _dd, cs, vars, bs):
  ba.flag(S.env.of(ev, vars), nn, cs, bs)

def Laws.bad_arg_allowed(nn, _sh, _lo, kind, _hp, _req, ev, _dd, cs, vars, bs, vv, h_env, h_in):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.env.bad.val(_, kind, nn, cs, bs) == None{} : Maybe<&2, S.Var>}
  e2 = Equal.sym(Bool, S.allowed(cs, vv), True{}, h_in)
  %e2 : {Bool.pick(Maybe<&2, S.Var>,
    Bool.and(Bool.not(S.env.flag.is(kind)), Bool.and(Bool.not(_),
      List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv))),
    Some{(nn, vv)}, None{}) == None{} : Maybe<&2, S.Var>}
  e3 = Equal.sym(Bool, Bool.and(Bool.not(S.env.flag.is(kind)), False{}), False{},
    ba.and_false(Bool.not(S.env.flag.is(kind))))
  %e3 : {Bool.pick(Maybe<&2, S.Var>, _, Some{(nn, vv)}, None{}) == None{} : Maybe<&2, S.Var>}
  {==}

def Laws.bad_arg_unbound(nn, _sh, _lo, kind, _hp, _req, ev, _dd, cs, vars, bs, vv, h_env, h_free):
  e1 = Equal.sym(Maybe<&2, String>, S.env.of(ev, vars), Some{vv}, h_env)
  %e1 : {S.env.bad.val(_, kind, nn, cs, bs) == None{} : Maybe<&2, S.Var>}
  e2 = Equal.sym(Bool, List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv), False{}, h_free)
  %e2 : {Bool.pick(Maybe<&2, S.Var>,
    Bool.and(Bool.not(S.env.flag.is(kind)), Bool.and(Bool.not(S.allowed(cs, vv)), _)),
    Some{(nn, vv)}, None{}) == None{} : Maybe<&2, S.Var>}
  e3 = Equal.sym(Bool, Bool.and(Bool.not(S.allowed(cs, vv)), False{}), False{},
    ba.and_false(Bool.not(S.allowed(cs, vv))))
  %e3 : {Bool.pick(Maybe<&2, S.Var>,
    Bool.and(Bool.not(S.env.flag.is(kind)), _),
    Some{(nn, vv)}, None{}) == None{} : Maybe<&2, S.Var>}
  e4 = Equal.sym(Bool, Bool.and(Bool.not(S.env.flag.is(kind)), False{}), False{},
    ba.and_false(Bool.not(S.env.flag.is(kind))))
  %e4 : {Bool.pick(Maybe<&2, S.Var>, _, Some{(nn, vv)}, None{}) == None{} : Maybe<&2, S.Var>}
  {==}
