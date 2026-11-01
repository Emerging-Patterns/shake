# proofs of laws/ValueBinds.bend
import Base
import ../src/cli.bend as S
import ../src/grow.bend as Grow
import ../laws/Kept.bend as L1
import ../laws/ValueBinds.bend as Laws
import ./lemmas/BindingsKept.bend as M1

# an option's value that is not flag-shaped and is allowed binds
def value.step(
  +tok: String,
  +name: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  h_flag: {S.looks_flag(tok) == False{} : Bool},
  h_ok: {S.allowed(S.parse.choices(S.by_name(args, name)), tok) == True{} : Bool}
) -> {S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen})
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}:
  e1 = Equal.sym(Bool, S.looks_flag(tok), False{}, h_flag)
  %e1 : {S.parse.step.need(_, name, tok, args, up, subs, path, bs, pos, raw, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}
  e2 = Equal.sym(Bool, S.allowed(S.parse.choices(S.by_name(args, name)), tok), True{}, h_ok)
  %e2 : {S.parse.take_choice(_, name, tok, args, up, subs, path, bs, pos, raw, seen)
    == S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen} : S.St}
  {==}

def Laws.value_binds(
  spec,
  pre,
  more,
  tok,
  name,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  raw,
  seen,
  found,
  h_at,
  h_flag,
  h_ok,
  h_done
):
  L1.kept(spec, pre, more, tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}, args, up, path,
      name, tok, bs, found, h_at,
    Equal.cong(S.St, Grow.View, xx => Grow.view(xx),
      S.parse.step(tok, S.St{S.Need{name}, args, up, subs, path, bs, pos, raw, seen}),
      S.St{S.Free{}, args, up, subs, path, S.Bind{name, tok} <> bs, pos, raw, seen},
      value.step(tok, name, args, up, subs, path, bs, pos, raw, seen, h_flag, h_ok)),
    h_done)
