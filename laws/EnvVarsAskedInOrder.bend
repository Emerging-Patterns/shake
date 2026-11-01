# The names `env_vars(spec)` asks `IO.get_env` for are the env vars of the
# arguments that have one, the root command's arguments first and then each
# subcommand's, depth first, each command's arguments in spec order.
import Base
import ../src/cli.bend as S

# LAW: `env_vars` asks for the root command's env vars, then its
# subcommands'
law env_names_root:
  for nn: String
  for ab: String
  for ver: Maybe<&2, String>
  for args: List<&2, S.Arg>
  for subs: List<&2, S.Sub>
  {S.env.names(S.Cli{nn, ab, ver, args, subs})
    == List.append(&2, String, S.env.names.args(args), S.env.names.forest(subs)) : List<&2, String>}

# LAW: a subcommand's env vars come before those of the subcommands under it,
# and those before its next sibling's
law env_names_forest:
  for nn: String
  for ab: String
  for args: List<&2, S.Arg>
  for kids: List<&2, S.Sub>
  for tt: List<&2, S.Sub>
  {S.env.names.forest(S.Sub{nn, ab, args, kids} <> tt)
    == List.append(&2, String, S.env.names.args(args),
      List.append(&2, String, S.env.names.forest(kids), S.env.names.forest(tt))) : List<&2, String>}

# LAW: an argument with an env var names it, in spec order
law env_names_some:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for +var: String
  for dd: Maybe<&2, String>
  for cs: List<&2, String>
  for tt: List<&2, S.Arg>
  {S.env.names.args(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{Some{var}, dd}, cs} <> tt)
    == var <> S.env.names.args(tt) : List<&2, String>}

# LAW: an argument with no env var names none
law env_names_none:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for dd: Maybe<&2, String>
  for cs: List<&2, String>
  for tt: List<&2, S.Arg>
  {S.env.names.args(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{None{}, dd}, cs} <> tt)
    == S.env.names.args(tt) : List<&2, String>}
