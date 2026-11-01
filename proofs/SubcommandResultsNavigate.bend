# proofs of laws/SubcommandResultsNavigate.bend
import Base
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../laws/SubcommandResultsNavigate.bend as Laws

def Laws.sub_name_leaf(_bs):
  {==}

def Laws.sub_name_node(_bs, _nn, _below):
  {==}

def Laws.sub_of_hit(_bs, nn, below):
  ee = Equal.sym(Bool, String.eq(nn, nn), True{}, Eq.string_eq_self(nn))
  %ee : {S.sub_of.pick(_, below) == Some{below} : Maybe<&2, S.Matched>}
  {==}

def Laws.sub_of_miss(_bs, nn, below, name, differ):
  ee = Equal.sym(Bool, String.eq(nn, name), False{}, differ)
  %ee : {S.sub_of.pick(_, below) == None{} : Maybe<&2, S.Matched>}
  {==}

def Laws.sub_of_leaf(_bs, _name):
  {==}

def Laws.path_of_leaf(_bs):
  {==}

def Laws.path_of_node(_bs, _nn, _below):
  {==}

def Laws.at_nil(found):
  match found:
    case S.Leaf{_b}:
      {==}
    case S.Node{_b, _n, _s}:
      {==}

# a walk down that found nothing finds nothing further down
def at_cons.none(rest: List<&2, String>) -> {S.at.go(rest, None{}) == None{} : Maybe<&2, S.Matched>}:
  match rest:
    case Nil{}:
      {==}
    case Con{_h, tt}:
      at_cons.none(tt)

# the rest of a walk down, from what the first name found
def at_cons.via(
  mm: Maybe<&2, S.Matched>,
  +rest: List<&2, String>
) -> {S.at.go(rest, mm) == Laws.at.via(mm, rest) : Maybe<&2, S.Matched>}:
  match mm:
    case None{}:
      at_cons.none(rest)
    case Some{_m}:
      {==}

def Laws.at_cons(found, name, rest):
  at_cons.via(S.sub_of(found, name), rest)
