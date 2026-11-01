# When the parse laws/EnvFallsBetweenWordsAndDefault.bend describes succeeds
# and an argument other than a flag, of a command on the selected path, has an
# env value outside its nonempty choices that the command's Matched binds to
# it, `parse_env` fails instead with `BadValue{at, name, value}` of the first
# such argument, the root command first and each command's arguments in spec
# order, where `at` is the selected path. A word's value outside the choices
# never binds (laws/ChoicesRestrictValues.bend), so only an argument filled
# from its env value can be bound to it. When that parse fails, `parse_env`
# fails with the same error.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: a failed parse fails `parse_env` with the same error
law env_check_fail:
  for spec: Shake.Cli
  for vars: List<&2, Shake.Var>
  for ee: Shake.ParseErr
  {S.env.check(spec, vars, Fail{ee}) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: a successful parse that bound no env value outside its choices is
# what `parse_env` answers
law env_check_good:
  for nn: String
  for ab: String
  for ver: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  for +mm: Shake.Matched
  for h_none: {S.env.bad.go(mm, args, subs, vars) == None{} : Maybe<&2, Shake.Var>}
  {S.env.check(S.Cli{nn, ab, ver, args, subs}, vars, Done{mm}) == Done{mm}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: a successful parse that bound an env value outside its choices fails
# with BadValue at the selected path
law env_check_bad:
  for nn: String
  for ab: String
  for ver: Maybe<&2, String>
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  for +mm: Shake.Matched
  for +name: String
  for +vv: String
  for h_bad: {S.env.bad.go(mm, args, subs, vars) == Some{(name, vv)} : Maybe<&2, Shake.Var>}
  {S.env.check(S.Cli{nn, ab, ver, args, subs}, vars, Done{mm}) == Fail{S.BadValue{Shake.path_of(mm), name, vv}}
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: the last command on the path is checked among its own arguments and
# bindings
law bad_go_leaf:
  for +bs: List<&2, S.Bind>
  for +args: List<&2, S.Arg>
  for subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  {S.env.bad.go(S.Leaf{bs}, args, subs, vars) == S.env.bad.args(args, vars, bs) : Maybe<&2, Shake.Var>}

# LAW: a command's own arguments come before the subcommand selected under it
law bad_go_root:
  for +bs: List<&2, S.Bind>
  for +name: String
  for +next: Shake.Matched
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  for +pp: Shake.Var
  for h_here: {S.env.bad.args(args, vars, bs) == Some{pp} : Maybe<&2, Shake.Var>}
  {S.env.bad.go(S.Node{bs, name, next}, args, subs, vars) == Some{pp} : Maybe<&2, Shake.Var>}

# LAW: with none among a command's own arguments, the subcommand selected
# under it is checked among its arguments and bindings
law bad_go_down:
  for +bs: List<&2, S.Bind>
  for +name: String
  for +next: Shake.Matched
  for +args: List<&2, S.Arg>
  for +subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  for h_none: {S.env.bad.args(args, vars, bs) == None{} : Maybe<&2, Shake.Var>}
  {S.env.bad.go(S.Node{bs, name, next}, args, subs, vars)
    == S.env.bad.go(next, S.env.sub.args(S.find_sub(subs, name)), S.env.sub.kids(S.find_sub(subs, name)), vars)
    : Maybe<&2, Shake.Var>}

# LAW: within a command, the first argument in spec order is the one reported
law bad_args_here:
  for +aa: S.Arg
  for +tt: List<&2, S.Arg>
  for +vars: List<&2, Shake.Var>
  for +bs: List<&2, S.Bind>
  for +pp: Shake.Var
  for h_here: {S.env.bad.arg(aa, vars, bs) == Some{pp} : Maybe<&2, Shake.Var>}
  {S.env.bad.args(aa <> tt, vars, bs) == Some{pp} : Maybe<&2, Shake.Var>}

# LAW: an argument that is fine passes the check on to the next
law bad_args_next:
  for +aa: S.Arg
  for +tt: List<&2, S.Arg>
  for +vars: List<&2, Shake.Var>
  for +bs: List<&2, S.Bind>
  for h_none: {S.env.bad.arg(aa, vars, bs) == None{} : Maybe<&2, Shake.Var>}
  {S.env.bad.args(aa <> tt, vars, bs) == S.env.bad.args(tt, vars, bs) : Maybe<&2, Shake.Var>}

# LAW: no command has a bad argument when there are no pairs
law bad_args_nil:
  for args: List<&2, S.Arg>
  for +bs: List<&2, S.Bind>
  {S.env.bad.args(args, [], bs) == None{} : Maybe<&2, Shake.Var>}

# LAW: an argument other than a flag whose env value is outside its choices
# and bound in its command is reported with that value
law bad_arg_some:
  for +nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for hp: String
  for req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +bs: List<&2, S.Bind>
  for +vv: String
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  for h_kind: {S.env.flag.is(kind) == False{} : Bool}
  for h_out: {S.allowed(cs, vv) == False{} : Bool}
  for h_bound: {List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv) == True{} : Bool}
  {S.env.bad.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars, bs) == Some{(nn, vv)}
    : Maybe<&2, Shake.Var>}

# LAW: an argument with no env value is never reported
law bad_arg_unset:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for bs: List<&2, S.Bind>
  for h_env: {S.env.of(ev, vars) == None{} : Maybe<&2, String>}
  {S.env.bad.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars, bs) == None{}
    : Maybe<&2, Shake.Var>}

# LAW: a flag is never reported
law bad_arg_flag:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for hp: String
  for req: Bool
  for ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for cs: List<&2, String>
  for vars: List<&2, Shake.Var>
  for bs: List<&2, S.Bind>
  {S.env.bad.arg(S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, dd}, cs}, vars, bs) == None{}
    : Maybe<&2, Shake.Var>}

# LAW: an env value its choices allow is never reported
law bad_arg_allowed:
  for +nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for hp: String
  for req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +bs: List<&2, S.Bind>
  for +vv: String
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  for h_in: {S.allowed(cs, vv) == True{} : Bool}
  {S.env.bad.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars, bs) == None{}
    : Maybe<&2, Shake.Var>}

# LAW: an env value its command does not bind is never reported
law bad_arg_unbound:
  for +nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for hp: String
  for req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +bs: List<&2, S.Bind>
  for +vv: String
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  for h_free: {List.contains(~String, ~String.eq, S.get_all.bind(bs, nn), vv) == False{} : Bool}
  {S.env.bad.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars, bs) == None{}
    : Maybe<&2, Shake.Var>}
