# The Options or Arguments line of an argument that has an env var `NAME`
# shows `[env: NAME]` after its help text, before its `[default: ...]` and
# `[possible values: ...]`, as clap's does; the line of one with no env var is
# what it would be without this row.
#
# also rests on: laws/ArgLineMark.bend
import Base
import ../src/cli.bend as S

# LAW: an option line shows the env var after the help text, before the
# default and the possible values
law help_env_shown:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for +var: String
  for +dd: Maybe<&2, String>
  for +cs: List<&2, String>
  {S.help.extra(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{Some{var}, dd}, cs})
    == (" [env: " ++ var ++ "]") ++ S.help.extra.go(S.text.of(dd, ""), cs) : String}

# LAW: an option line with no env var shows only the default and the possible
# values, as before
law help_env_none:
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for kind: S.ArgKind
  for hp: String
  for req: Bool
  for +dd: Maybe<&2, String>
  for +cs: List<&2, String>
  {S.help.extra(S.Arg{nn, sh, lo, kind, hp, req, S.Fallback{None{}, dd}, cs})
    == S.help.extra.go(S.text.of(dd, ""), cs) : String}
