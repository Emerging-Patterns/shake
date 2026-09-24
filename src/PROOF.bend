# shake: the proofs. `bend src/PROOF.bend` is the gate.
import Base
import ../src/cli.bend as S
import ../src/eq.bend as Eq
import ../src/args.bend as Args
import ./LAWS.bend as Laws

def Laws.looks_flag_long(_ss):
  {==}

def Laws.allowed_any(_vv):
  {==}

def Laws.get_nil(_name):
  {==}

def Laws.on_nil(_name):
  {==}

def Laws.err_text_help(_spec, _path):
  {==}

def Laws.err_text_iff(spec, err):
  match spec err:
    case S.Cli{_n, _a, _v, _g, _s} S.UnknownFlag{_flag}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Missing{_name}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.BadValue{_name, _value}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.NeedHelp{_path}:
      {==}
    case S.Cli{_n, _a, _v, _g, _s} S.Unexpected{_arg}:
      {==}

def Laws.hit_append(bb, _vv, _xs, _ys):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bind_values_append(bs, cs, name):
  match bs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Bind{+nn, +vv}:
          ih = Equal.sym(List<&2, String>,
            S.get_all.bind(List.append(&2, S.Bind, tt, cs), name),
            List.append(&2, String, S.get_all.bind(tt, name), S.get_all.bind(cs, name)),
            Laws.bind_values_append(tt, cs, name))
          %ih : {S.get_all.bind.hit(String.eq(nn, name), vv, _)
            == List.append(&2, String,
              S.get_all.bind.hit(String.eq(nn, name), vv, S.get_all.bind(tt, name)),
              S.get_all.bind(cs, name)) : List<&2, String>}
          Laws.hit_append(String.eq(nn, name), vv, S.get_all.bind(tt, name),
            S.get_all.bind(cs, name))

def Laws.last_snoc(xs, vv, _dflt):
  match xs:
    case Nil{}:
      {==}
    case Con{hh, tt}:
      Laws.last_snoc(tt, vv, hh)

def Laws.get_all_append(_path, bs, cs, name):
  Laws.bind_values_append(bs, cs, name)

def Laws.get_all_hit(_path, name, vv):
  ee = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %ee : {S.get_all.bind.hit(_, vv, []) == [vv] : List<&2, String>}
  {==}

def Laws.get_all_miss(_path, other, name, vv, differ):
  ee = Equal.sym(Bool, String.eq(other, name), False{}, differ)
  %ee : {S.get_all.bind.hit(_, vv, []) == [] : List<&2, String>}
  {==}

def Laws.get_last(_path, bs, cs, name, vv, after):
  e1 = Equal.sym(List<&2, String>,
    S.get_all.bind(List.append(&2, S.Bind, bs, S.Bind{name, vv} <> cs), name),
    List.append(&2, String, S.get_all.bind(bs, name), S.get_all.bind(S.Bind{name, vv} <> cs, name)),
    Laws.bind_values_append(bs, S.Bind{name, vv} <> cs, name))
  %e1 : {S.get.last(_, "") == vv : String}
  e2 = Equal.sym(Bool, String.eq(name, name), True{}, Eq.string_eq_self(name))
  %e2 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name),
    S.get_all.bind.hit(_, vv, S.get_all.bind(cs, name))), "") == vv : String}
  e3 = Equal.sym(List<&2, String>, S.get_all.bind(cs, name), [], after)
  %e3 : {S.get.last(List.append(&2, String, S.get_all.bind(bs, name), vv <> _), "")
    == vv : String}
  Laws.last_snoc(S.get_all.bind(bs, name), vv, "")

def Laws.get_none(_path, bs, name, none):
  ee = Equal.sym(List<&2, String>, S.get_all.bind(bs, name), [], none)
  %ee : {S.get.last(_, "") == "" : String}
  {==}

def Laws.on_get(_found, _name):
  {==}

def Laws.path_of_path(_path, _bs):
  {==}

def Laws.copy_keeps(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      ih = Equal.sym(List<&1, String>, Laws.down(Args.copy(tt)), tt, Laws.copy_keeps(tt))
      %ih : {hh <> _ == hh <> tt : List<&1, String>}
      {==}
