# get_all and hits over appended bindings
import Base
import ../../src/cli.bend as S
import ../../laws/BindValuesAppend.bend as L1
import ../../laws/HitAppend.bend as L2

def L2.hit_append(bb, _vv, _xs, _ys):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

def L1.bind_values_append(bs, cs, name):
  match bs:
    case Nil{}:
      {==}
    case Con{hh, +tt}:
      match hh:
        case S.Bind{+nn, +vv}:
          ih = Equal.sym(List<&2, String>,
            S.get_all.bind(List.append(&2, S.Bind, tt, cs), name),
            List.append(&2, String, S.get_all.bind(tt, name), S.get_all.bind(cs, name)),
            L1.bind_values_append(tt, cs, name))
          %ih : {S.get_all.bind.hit(String.eq(nn, name), vv, _)
            == List.append(&2, String,
              S.get_all.bind.hit(String.eq(nn, name), vv, S.get_all.bind(tt, name)),
              S.get_all.bind(cs, name)) : List<&2, String>}
          L2.hit_append(String.eq(nn, name), vv, S.get_all.bind(tt, name),
            S.get_all.bind(cs, name))
