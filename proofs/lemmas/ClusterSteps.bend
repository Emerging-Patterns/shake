# one letter of a short cluster, read in a free walker
import Base
import ../../src/cli.bend as S

# one letter of a cluster in a free walker, once the argument it spells is
# known: `take_arg` with the value the letter's kind gives, then the rest,
# ended or not as the kind says
def cl.step(
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +aa: S.Arg,
  h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{aa} : Maybe<&2, S.Arg>}
) -> {S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{})
    == S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs,
        path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest)) : S.St}:
  ee = Equal.sym(Maybe<&2, S.Arg>, S.by_short(args, SCon{cc, SNil{}}), Some{aa}, h_found)
  %ee : {S.cluster(rest, orig, S.parse.take_arg(_, S.cluster.val(_, rest), orig, args, up, subs, path, bs, pos, raw,
      seen), S.cluster.ends(_, rest))
    == S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs, path, bs,
      pos, raw, seen), S.cluster.ends(Some{aa}, rest)) : S.St}
  {==}

# the same, the other way round, for rewriting a goal about the cluster
def cl.back(
  +cc: Char,
  +rest: String,
  +orig: String,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +pos: List<&2, S.Arg>,
  +raw: Bool,
  +seen: Bool,
  +aa: S.Arg,
  h_found: {S.by_short(args, SCon{cc, SNil{}}) == Some{aa} : Maybe<&2, S.Arg>}
) -> {S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs,
    path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest))
    == S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{}) : S.St}:
  Equal.sym(S.St, S.cluster(SCon{cc, rest}, orig, S.St{S.Free{}, args, up, subs, path, bs, pos, raw, seen}, False{}),
    S.cluster(rest, orig, S.parse.take_arg(Some{aa}, S.cluster.val(Some{aa}, rest), orig, args, up, subs, path, bs, pos,
      raw, seen), S.cluster.ends(Some{aa}, rest)),
    cl.step(cc, rest, orig, args, up, subs, path, bs, pos, raw, seen, aa, h_found))
