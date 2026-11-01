# `check_reads(spec, reads)` reports exactly one error for each read in
# `reads` that is wrong, in the order of `reads`, and nothing for a read that
# is right: `NoCommand{path}` when a name of its path is not a subcommand of
# the command before it, the root first; otherwise `NoArg{path, name}` when
# the command its path names has no argument named `name`; otherwise, for a
# flag read (`read_flag`), `NotFlag{path, name}` when that argument is not a
# flag, and for a value read (`read_value`), `IsFlag{path, name}` when it is
# one. It reports nothing else.
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/check.bend as K

# the root command as a subcommand, to walk a path from
def root_sub(app: Shake.Cli) -> S.Sub:
  S.Cli{+name, +about, _v, args, subs} = app
  S.Sub{name, about, args, subs}

# the subcommand named `name` of a found command
def sub_named(here: Maybe<&2, S.Sub>, +name: String) -> Maybe<&2, S.Sub>:
  match here:
    case None{}:
      None{}
    case Some{ss}:
      S.Sub{_n, _a, _g, subs} = ss
      S.find_sub(subs, name)

# the command a path names below a found one, each name a subcommand of the
# command before it, or None
def named_cmd(path: List<&2, String>, here: Maybe<&2, S.Sub>) -> Maybe<&2, S.Sub>:
  match path:
    case Nil{}:
      here
    case Con{+hh, tt}:
      named_cmd(tt, sub_named(here, hh))

# whether an argument kind is a flag
def is_flag(kk: S.ArgKind) -> Bool:
  match kk:
    case S.Flag{}:
      True{}
    case _other:
      False{}

# LAW: no reads, no reports
law reads_nil:
  for +spec: Shake.Cli
  {Shake.check_reads(spec, []) == [] : List<&2, K.ReadErr>}

# LAW: the reports of each read, in the order of the reads
law reads_con:
  for +spec: Shake.Cli
  for rr: K.Read
  for rs: List<&2, K.Read>
  {Shake.check_reads(spec, rr <> rs) == List.append(&2, K.ReadErr, K.read(spec, rr), Shake.check_reads(spec, rs))
    : List<&2, K.ReadErr>}

# LAW: a read whose path names no command is reported as that
law read_no_command:
  for +spec: Shake.Cli
  for +path: List<&2, String>
  for +name: String
  for want: K.Want
  for h_cmd: {named_cmd(path, Some{root_sub(spec)}) == None{} : Maybe<&2, S.Sub>}
  {K.read(spec, K.Read{path, name, want}) == [K.NoCommand{path}] : List<&2, K.ReadErr>}

# LAW: a read of a name no argument of its command has is reported as that
law read_no_arg:
  for +spec: Shake.Cli
  for +path: List<&2, String>
  for +name: String
  for want: K.Want
  for sn: String
  for sa: String
  for +sargs: List<&2, S.Arg>
  for ssubs: List<&2, S.Sub>
  for h_cmd: {named_cmd(path, Some{root_sub(spec)}) == Some{S.Sub{sn, sa, sargs, ssubs}} : Maybe<&2, S.Sub>}
  for h_arg: {S.by_name(sargs, name) == None{} : Maybe<&2, S.Arg>}
  {K.read(spec, K.Read{path, name, want}) == [K.NoArg{path, name}] : List<&2, K.ReadErr>}

# LAW: a flag read is reported exactly when its argument is not a flag
law read_flag:
  for +spec: Shake.Cli
  for +path: List<&2, String>
  for +name: String
  for sn: String
  for sa: String
  for +sargs: List<&2, S.Arg>
  for ssubs: List<&2, S.Sub>
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for hp: String
  for rq: Bool
  for fb: S.Fallback
  for cs: List<&2, String>
  for h_cmd: {named_cmd(path, Some{root_sub(spec)}) == Some{S.Sub{sn, sa, sargs, ssubs}} : Maybe<&2, S.Sub>}
  for h_arg: {S.by_name(sargs, name) == Some{S.Arg{nn, sh, lo, kind, hp, rq, fb, cs}} : Maybe<&2, S.Arg>}
  {K.read(spec, K.Read{path, name, K.WantFlag{}})
    == K.reads.one(Bool.not(is_flag(kind)), K.NotFlag{path, name}) : List<&2, K.ReadErr>}

# LAW: a value read is reported exactly when its argument is a flag
law read_value:
  for +spec: Shake.Cli
  for +path: List<&2, String>
  for +name: String
  for sn: String
  for sa: String
  for +sargs: List<&2, S.Arg>
  for ssubs: List<&2, S.Sub>
  for nn: String
  for sh: Maybe<&2, String>
  for lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for hp: String
  for rq: Bool
  for fb: S.Fallback
  for cs: List<&2, String>
  for h_cmd: {named_cmd(path, Some{root_sub(spec)}) == Some{S.Sub{sn, sa, sargs, ssubs}} : Maybe<&2, S.Sub>}
  for h_arg: {S.by_name(sargs, name) == Some{S.Arg{nn, sh, lo, kind, hp, rq, fb, cs}} : Maybe<&2, S.Arg>}
  {K.read(spec, K.Read{path, name, K.WantValue{}}) == K.reads.one(is_flag(kind), K.IsFlag{path, name})
    : List<&2, K.ReadErr>}
