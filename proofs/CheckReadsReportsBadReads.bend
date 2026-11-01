# proofs of laws/CheckReadsReportsBadReads.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/check.bend as K
import ../laws/CheckReadsReportsBadReads.bend as Laws

def Laws.reads_nil(_spec):
  {==}

def Laws.reads_con(_spec, _rr, _rs):
  {==}

# the code's walk down a path is the law's
def rd.down(
  here: Maybe<&2, S.Sub>,
  +name: String
) -> {K.reads.down(here, name) == Laws.sub_named(here, name) : Maybe<&2, S.Sub>}:
  match here:
    case None{}:
      {==}
    case Some{ss}:
      match ss:
        case S.Sub{_n, _a, _g, _s}:
          {==}

# the command a path names, as the code finds its arguments
def rd.cmd(
  path: List<&2, String>,
  +here: Maybe<&2, S.Sub>
) -> {K.reads.cmd(path, here) == K.reads.args(Laws.named_cmd(path, here)) : Maybe<&2, List<&2, S.Arg>>}:
  match path:
    case Nil{}:
      {==}
    case Con{+hh, +tt}:
      Equal.trans(Maybe<&2, List<&2, S.Arg>>, K.reads.cmd(tt, K.reads.down(here, hh)),
        K.reads.cmd(tt, Laws.sub_named(here, hh)), K.reads.args(Laws.named_cmd(tt, Laws.sub_named(here, hh))),
        Equal.cong(Maybe<&2, S.Sub>, Maybe<&2, List<&2, S.Arg>>, xx => K.reads.cmd(tt, xx), K.reads.down(here, hh),
          Laws.sub_named(here, hh), rd.down(here, hh)),
        rd.cmd(tt, Laws.sub_named(here, hh)))

# a read, its command found as the law finds it
def rd.base(
  spec: Shake.Cli,
  +path: List<&2, String>,
  +name: String,
  +want: K.Want,
  +found: Maybe<&2, S.Sub>,
  h_cmd: {Laws.named_cmd(path, Some{Laws.root_sub(spec)}) == found : Maybe<&2, S.Sub>}
) -> {K.read(spec, K.Read{path, name, want}) == K.reads.at(K.reads.args(found), want, path, name)
    : List<&2, K.ReadErr>}:
  match spec:
    case S.Cli{+bin, +about, _v, +args, +subs}:
      +here = {Some{S.Sub{bin, about, args, subs}} : Maybe<&2, S.Sub>}
      Equal.cong(Maybe<&2, List<&2, S.Arg>>, List<&2, K.ReadErr>, xx => K.reads.at(xx, want, path, name),
        K.reads.cmd(path, here), K.reads.args(found),
        Equal.trans(Maybe<&2, List<&2, S.Arg>>, K.reads.cmd(path, here), K.reads.args(Laws.named_cmd(path, here)),
          K.reads.args(found), rd.cmd(path, here),
          Equal.cong(Maybe<&2, S.Sub>, Maybe<&2, List<&2, S.Arg>>, xx => K.reads.args(xx),
            Laws.named_cmd(path, here), found, h_cmd)))

def Laws.read_no_command(spec, path, name, want, h_cmd):
  rd.base(spec, path, name, want, None{}, h_cmd)

# a read of the argument a command's arguments find under its name
def rd.arg(
  +spec: Shake.Cli,
  +path: List<&2, String>,
  +name: String,
  +want: K.Want,
  +sn: String,
  +sa: String,
  +sargs: List<&2, S.Arg>,
  +ssubs: List<&2, S.Sub>,
  +fa: Maybe<&2, S.Arg>,
  h_cmd: {Laws.named_cmd(path, Some{Laws.root_sub(spec)}) == Some{S.Sub{sn, sa, sargs, ssubs}} : Maybe<&2, S.Sub>},
  h_arg: {S.by_name(sargs, name) == fa : Maybe<&2, S.Arg>}
) -> {K.read(spec, K.Read{path, name, want}) == K.reads.arg(fa, want, path, name) : List<&2, K.ReadErr>}:
  Equal.trans(List<&2, K.ReadErr>, K.read(spec, K.Read{path, name, want}),
    K.reads.arg(S.by_name(sargs, name), want, path, name), K.reads.arg(fa, want, path, name),
    rd.base(spec, path, name, want, Some{S.Sub{sn, sa, sargs, ssubs}}, h_cmd),
    Equal.cong(Maybe<&2, S.Arg>, List<&2, K.ReadErr>, xx => K.reads.arg(xx, want, path, name), S.by_name(sargs, name),
      fa, h_arg))

def Laws.read_no_arg(spec, path, name, want, sn, sa, sargs, ssubs, h_cmd, h_arg):
  rd.arg(spec, path, name, want, sn, sa, sargs, ssubs, None{}, h_cmd, h_arg)

# the code's flag test is the law's
def rd.flag(kind: S.ArgKind) -> {K.reads.flag(kind) == Laws.is_flag(kind) : Bool}:
  match kind:
    case S.Flag{}:
      {==}
    case S.Opt{}:
      {==}
    case S.Pos{}:
      {==}
    case S.Rest{}:
      {==}
    case S.Many{}:
      {==}

def Laws.read_flag(spec, path, name, sn, sa, sargs, ssubs, nn, sh, lo, kind, hp, rq, fb, cs, h_cmd, h_arg):
  Equal.trans(List<&2, K.ReadErr>, K.read(spec, K.Read{path, name, K.WantFlag{}}),
    K.reads.one(Bool.not(K.reads.flag(kind)), K.NotFlag{path, name}),
    K.reads.one(Bool.not(Laws.is_flag(kind)), K.NotFlag{path, name}),
    rd.arg(spec, path, name, K.WantFlag{}, sn, sa, sargs, ssubs, Some{S.Arg{nn, sh, lo, kind, hp, rq, fb, cs}}, h_cmd,
      h_arg),
    Equal.cong(Bool, List<&2, K.ReadErr>, xx => K.reads.one(Bool.not(xx), K.NotFlag{path, name}), K.reads.flag(kind),
      Laws.is_flag(kind), rd.flag(kind)))

def Laws.read_value(spec, path, name, sn, sa, sargs, ssubs, nn, sh, lo, kind, hp, rq, fb, cs, h_cmd, h_arg):
  Equal.trans(List<&2, K.ReadErr>, K.read(spec, K.Read{path, name, K.WantValue{}}),
    K.reads.one(K.reads.flag(kind), K.IsFlag{path, name}),
    K.reads.one(Laws.is_flag(kind), K.IsFlag{path, name}),
    rd.arg(spec, path, name, K.WantValue{}, sn, sa, sargs, ssubs, Some{S.Arg{nn, sh, lo, kind, hp, rq, fb, cs}}, h_cmd,
      h_arg),
    Equal.cong(Bool, List<&2, K.ReadErr>, xx => K.reads.one(xx, K.IsFlag{path, name}), K.reads.flag(kind),
      Laws.is_flag(kind), rd.flag(kind)))
