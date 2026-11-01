# `parse_env(spec, words, vars)` reads `words` exactly as `parse` reads them
# against `spec` with every argument's default, in every command, replaced by
# its **fallback**, and answers what that parse answers, except as
# laws/EnvValueOutsideChoicesFails.bend says. An argument's fallback is its
# env value when it has one and is not a flag; for a flag with an env value,
# `true` when that value, lowercased, is none of `0`, `false`, `no`, `off`,
# `n` and `f`, and no fallback otherwise; and for an argument with no env
# value, its default. So a value the words bind wins over the env value and
# the env value over the default (laws/DefaultsFillUnbound.bend), an argument
# with a fallback is filled by it and needs nothing from the words to satisfy
# `required` (laws/RequiredMustBind.bend), a required positional with a
# fallback does not block a subcommand (laws/SubcommandSelects.bend), and
# `parse_env(spec, words, [])` is `parse(spec, words)`.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S

# LAW: `env` gives an argument its env var and keeps the rest of it
law env_sets:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for ev: Maybe<&2, String>
  for +dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +var: String
  {Shake.env(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, var)
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{Some{var}, dd}, cs} : S.Arg}

# LAW: an argument with no env var has no env value
law env_of_none:
  for vars: List<&2, Shake.Var>
  {S.env.of(None{}, vars) == None{} : Maybe<&2, String>}

# LAW: an env var no pair names has no env value
law env_of_nil:
  for var: String
  {S.env.of(Some{var}, []) == None{} : Maybe<&2, String>}

# LAW: the first pair an env var names gives its env value, when its value
# is not empty
law env_of_hit:
  for +var: String
  for +nn: String
  for +vv: String
  for rest: List<&2, Shake.Var>
  for h_eq: {String.eq(nn, var) == True{} : Bool}
  for h_full: {String.is_empty(vv) == False{} : Bool}
  {S.env.of(Some{var}, (nn, vv) <> rest) == Some{vv} : Maybe<&2, String>}

# LAW: an empty value in the first pair an env var names gives no env value,
# whatever later pairs hold
law env_of_empty:
  for +var: String
  for +nn: String
  for +vv: String
  for rest: List<&2, Shake.Var>
  for h_eq: {String.eq(nn, var) == True{} : Bool}
  for h_empty: {String.is_empty(vv) == True{} : Bool}
  {S.env.of(Some{var}, (nn, vv) <> rest) == None{} : Maybe<&2, String>}

# LAW: a pair named otherwise is passed over
law env_of_skip:
  for +var: String
  for +nn: String
  for +vv: String
  for +rest: List<&2, Shake.Var>
  for h_eq: {String.eq(nn, var) == False{} : Bool}
  {S.env.of(Some{var}, (nn, vv) <> rest) == S.env.of(Some{var}, rest) : Maybe<&2, String>}

# the env values that turn a flag off, lowercased
def off_words() -> List<&2, String>:
  ["0", "false", "no", "off", "n", "f"]

# LAW: an argument other than a flag that has an env value falls back to it
law fallback_env:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +vv: String
  for h_kind: {S.env.flag.is(kind) == False{} : Bool}
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  {S.resolve.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars)
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, Some{vv}}, cs} : S.Arg}

# LAW: a flag with an env value that, lowercased, is not an off word falls
# back to `true`
law fallback_flag_on:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +vv: String
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  for h_on: {S.allowed.ok(off_words(), String.to_lower(vv)) == False{} : Bool}
  {S.resolve.arg(S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, dd}, cs}, vars)
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, Some{"true"}}, cs} : S.Arg}

# LAW: a flag with an env value that, lowercased, is an off word has no
# fallback
law fallback_flag_off:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +hp: String
  for +req: Bool
  for +ev: Maybe<&2, String>
  for dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for +vv: String
  for h_env: {S.env.of(ev, vars) == Some{vv} : Maybe<&2, String>}
  for h_off: {S.allowed.ok(off_words(), String.to_lower(vv)) == True{} : Bool}
  {S.resolve.arg(S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, dd}, cs}, vars)
    == S.Arg{nn, sh, lo, S.Flag{}, hp, req, S.Fallback{ev, None{}}, cs} : S.Arg}

# LAW: an argument with no env value falls back to its default
law fallback_default:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +ev: Maybe<&2, String>
  for +dd: Maybe<&2, String>
  for +cs: List<&2, String>
  for +vars: List<&2, Shake.Var>
  for h_env: {S.env.of(ev, vars) == None{} : Maybe<&2, String>}
  {S.resolve.arg(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs}, vars)
    == S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{ev, dd}, cs} : S.Arg}

# LAW: a spec's arguments are resolved in the root command and below it
law resolve_spec:
  for +nn: String
  for +ab: String
  for +ver: Maybe<&2, String>
  for args: List<&2, S.Arg>
  for subs: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  {S.resolve(S.Cli{nn, ab, ver, args, subs}, vars)
    == S.Cli{nn, ab, ver, S.resolve.args(args, vars), S.resolve.subs(subs, vars)} : S.Cli}

# LAW: a command's arguments are resolved one by one, in order
law resolve_args_con:
  for aa: S.Arg
  for tt: List<&2, S.Arg>
  for +vars: List<&2, Shake.Var>
  {S.resolve.args(aa <> tt, vars) == S.resolve.arg(aa, vars) <> S.resolve.args(tt, vars) : List<&2, S.Arg>}

# LAW: a subcommand's arguments are resolved, and every subcommand under it
law resolve_subs_con:
  for +nn: String
  for +ab: String
  for args: List<&2, S.Arg>
  for kids: List<&2, S.Sub>
  for tt: List<&2, S.Sub>
  for +vars: List<&2, Shake.Var>
  {S.resolve.subs(S.Sub{nn, ab, args, kids} <> tt, vars)
    == S.Sub{nn, ab, S.resolve.args(args, vars), S.resolve.subs(kids, vars)} <> S.resolve.subs(tt, vars)
    : List<&2, S.Sub>}

# LAW: `parse_env` is `parse` against the spec with every default replaced by
# its fallback, then the check laws/EnvValueOutsideChoicesFails.bend describes
law env_parse:
  for +spec: Shake.Cli
  for ws: List<&2, String>
  for +vars: List<&2, Shake.Var>
  {Shake.parse_env(spec, ws, vars) == S.env.check(spec, vars, Shake.parse(S.resolve(spec, vars), ws))
    : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: with no pairs, `parse_env` is `parse`
law env_none:
  for +spec: Shake.Cli
  for ws: List<&2, String>
  {Shake.parse_env(spec, ws, []) == Shake.parse(spec, ws) : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
