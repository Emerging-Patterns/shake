# proofs of laws/BuiltinsListed.bend
import Base
import ../src/cli.bend as S
import ../laws/BuiltinsListed.bend as Laws

# the help row is the law's
def bi.help(
  long: Maybe<&2, S.Arg>,
  short: Maybe<&2, S.Arg>
) -> {S.help.help_row(long, short) == Laws.help_rows.of(long, short) : List<&2, S.Arg>}:
  match long:
    case None{}:
      match short:
        case None{}:
          {==}
        case Some{_a}:
          {==}
    case Some{_a}:
      {==}

# the version row of a page with a version is the law's
def bi.vrow(
  +vv: String,
  long: Maybe<&2, S.Arg>,
  short: Maybe<&2, S.Arg>
) -> {S.help.version_row(Some{vv}, long, short) == Laws.version_rows.of(long, short) : List<&2, S.Arg>}:
  match long:
    case None{}:
      match short:
        case None{}:
          {==}
        case Some{_a}:
          {==}
    case Some{_a}:
      {==}

# the version row is the law's
def bi.version(
  +args: List<&2, S.Arg>,
  version: Maybe<&2, String>
) -> {S.help.version_row(version, S.by_long(args, "version"), S.by_short(args, "V")) == Laws.version_rows(args, version)
    : List<&2, S.Arg>}:
  match version:
    case None{}:
      {==}
    case Some{+vv}:
      bi.vrow(vv, S.by_long(args, "version"), S.by_short(args, "V"))

def Laws.builtins_listed(args, version):
  +hr = S.help.help_row(S.by_long(args, "help"), S.by_short(args, "h"))
  +vr = S.help.version_row(version, S.by_long(args, "version"), S.by_short(args, "V"))
  Equal.trans(List<&2, S.Arg>, List.append(&2, S.Arg, hr, vr), List.append(&2, S.Arg, Laws.help_rows(args), vr),
    List.append(&2, S.Arg, Laws.help_rows(args), Laws.version_rows(args, version)),
    Equal.cong(List<&2, S.Arg>, List<&2, S.Arg>, xs => List.append(&2, S.Arg, xs, vr), hr, Laws.help_rows(args),
      bi.help(S.by_long(args, "help"), S.by_short(args, "h"))),
    Equal.cong(List<&2, S.Arg>, List<&2, S.Arg>, xs => List.append(&2, S.Arg, Laws.help_rows(args), xs), vr,
      Laws.version_rows(args, version), bi.version(args, version)))
