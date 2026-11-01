# `version_of(spec, err)` is `Some{name ++ " " ++ version}`, the root
# command's name and the spec's version, when `err` is `NeedVersion{}` and the
# spec has a version, and `None` otherwise.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ./defs/VersionRequest.bend as D1

# LAW: a request for the version reads as the root's name and the version
law version_of_some:
  for +name: String
  for about: String
  for +ver: String
  for args: List<&2, S.Arg>
  for subs: List<&2, S.Sub>
  {Shake.version_of(S.Cli{name, about, Some{ver}, args, subs}, S.NeedVersion{}) == Some{name ++ " " ++ ver}
    : Maybe<&2, String>}

# LAW: a spec with no version reads no version, whatever the error
law version_of_none:
  for +name: String
  for about: String
  for args: List<&2, S.Arg>
  for subs: List<&2, S.Sub>
  for err: Shake.ParseErr
  {Shake.version_of(S.Cli{name, about, None{}, args, subs}, err) == None{} : Maybe<&2, String>}

# LAW: an error that is no request for the version reads no version
law version_of_other:
  for +spec: Shake.Cli
  for err: Shake.ParseErr
  for h_err: {D1.version.is(err) == False{} : Bool}
  {Shake.version_of(spec, err) == None{} : Maybe<&2, String>}
