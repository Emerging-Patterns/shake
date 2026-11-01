# proofs of laws/GetReadsOwnBindings.bend
import Base
import ../main.bend as Shake
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../laws/BindValuesAppend.bend as L1
import ../laws/GetReadsOwnBindings.bend as Laws
import ../laws/LastSnoc.bend as L2
import ./lemmas/AppendedBindings.bend as M1
import ./lemmas/LastOfSnoc.bend as M2

def Laws.get_all_append(bs, cs, name):
  L1.bind_values_append(bs, cs, name)

def Laws.get_all_hit(name, vv):
  ee = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %ee : {S.get_all.bind.hit(_, vv, []) == [vv] : List<&2, String>}
  {==}

def Laws.get_all_miss(other, name, vv, differ):
  ee = Equal.sym(Bool, String.eq(other, name), False{}, differ)
  %ee : {S.get_all.bind.hit(_, vv, []) == [] : List<&2, String>}
  {==}

def Laws.get_last(bs, cs, name, vv, after):
  e1 = Equal.sym(List<&2, String>,
    S.get_all.bind(List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs), name),
    List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(S.Bind{name, vv} <> cs, name)),
    L1.bind_values_append(bs, S.Bind{name, vv} <> cs, name))
  %e1 : {S.get.last(_, None{}) == Some{vv} : Maybe<&2, String>}
  e2 = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %e2 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name),
    S.get_all.bind.hit(_, vv, S.get_all.bind(cs, name))), None{}) == Some{vv}
    : Maybe<&2, String>}
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(cs, name), [], after)
  %e3 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name), vv <> _), None{})
    == Some{vv} : Maybe<&2, String>}
  L2.last_snoc(S.get_all.bind(bs, name), vv, None{})

def Laws.get_none(bs, name, none):
  ee = Equal.sym(List<&2, String>, S.get_all.bind(bs, name), [], none)
  %ee : {S.get.last(_, None{}) == None{} : Maybe<&2, String>}
  {==}

def Laws.on_some(found, name, vv, h_get):
  ee = Equal.sym(Maybe<&2, String>, Shake.get(found, name), Some{vv}, h_get)
  %ee : {S.on.of(_) == String.eq(vv, "true") : Bool}
  {==}

def Laws.on_none(found, name, h_get):
  ee = Equal.sym(Maybe<&2, String>, Shake.get(found, name), None{}, h_get)
  %ee : {S.on.of(_) == False{} : Bool}
  {==}

def Laws.get_all_node(_bs, _nn, _below, _name):
  {==}

def Laws.get_node(_bs, _nn, _below, _name):
  {==}
