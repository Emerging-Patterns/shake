# proofs of laws/HelpFollowsPath.bend
import Base
import ../src/cli.bend as S
import ../laws/HelpFollowsPath.bend as Laws

def Laws.reach_child(bin, about, version, args, subs, usage, name, sn, sa, sargs, ssubs, h_sub):
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, name), Some{S.Sub{sn, sa, sargs, ssubs}}, h_sub)
  %ee : {S.help.step.go(_, bin, about, version, args, subs, name, usage)
    == S.How{sn, sa, None{}, sargs, ssubs, usage ++ " " ++ name} : S.How}
  {==}

def Laws.reach_skip(bin, about, version, args, subs, usage, name, h_sub):
  ee = Equal.sym(Maybe<&2, S.Sub>, S.find_sub(subs, name), None{}, h_sub)
  %ee : {S.help.step.go(_, bin, about, version, args, subs, name, usage) == S.How{bin, about, version, args,
      subs, usage}
    : S.How}
  {==}
