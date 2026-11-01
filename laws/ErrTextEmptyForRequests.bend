# `err_text(spec, err)` is empty exactly when `help_path(err)` is `Some` or
# `err` is `NeedVersion{}`, that is, when the parse failed with a request for
# help or for the version.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/VersionRequest.bend as D1

# LAW: a request for help has no error text, for every spec and path
law err_text_help:
  for spec: Shake.Cli
  for path: List<&2, String>
  {Shake.err_text(spec, S.NeedHelp{path}) == "" : String}

# LAW: a request for the version has no error text, for every spec
law err_text_version:
  for spec: Shake.Cli
  {Shake.err_text(spec, S.NeedVersion{}) == "" : String}

# LAW: the error text is empty exactly when the parse asked for help or for
# the version
law err_text_iff:
  for +spec: Shake.Cli
  for +err: Shake.ParseErr
  {String.is_empty(Shake.err_text(spec, err))
    == Bool.or(Maybe.is_some(&2, List<&2, String>, Shake.help_path(err)), D1.version.is(err)) : Bool}
