# Before `--`, a plain word that names a subcommand of the current command
# selects it: the selected path gains that name, its arguments become current,
# and the bindings made so far stay with the command that made them; the
# subcommand's own bindings start empty. When a pending positional of the
# current command is required, has no default and is not a rest, the parse
# fails instead with `Missing{name}` of the first such one; a rest positional
# does not block a subcommand, and laws/RequiredMustBind.bend checks it when the words end.
#
# also rests on: laws/EnterMissing.bend, laws/EnterStep.bend
import Base
import ../src/cli.bend as S
import ./defs/BlockingPositional.bend as D1

# whether no pending positional blocks a subcommand
def none_block(pos: List<&2, S.Arg>) -> Bool:
  match pos:
    case Nil{}:
      True{}
    case Con{hh, tt}:
      Bool.and(Bool.not(D1.blocks(hh)), none_block(tt))

# LAW: with no pending positional that is required, has no default and is not
# a rest, nothing blocks a subcommand
law none_blocking:
  for pos: List<&2, S.Arg>
  for +h_none: {none_block(pos) == True{} : Bool}
  {S.parse.first_req(pos) == None{} : Maybe<&2, String>}

# LAW: the positional that blocks a subcommand is the first pending one that is
# required, has no default and is not a rest
law first_blocking:
  for pa: List<&2, S.Arg>
  for +nm: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +ev: Maybe<&2, String>
  for +cs: List<&2, String>
  for +qa: List<&2, S.Arg>
  for +h_pa: {none_block(pa) == True{} : Bool}
  for h_kind: {S.rest.is.kind(kind) == False{} : Bool}
  {S.parse.first_req(List.append(&2, S.Arg, pa, S.Arg{nm, sh, lo, kind, hp, True{}, S.Fallback{ev, None{}},
      cs} <> qa)) == Some{nm}
    : Maybe<&2, String>}
