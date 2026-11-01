# proofs of laws/PlainWordIsNeverOption.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/PlainWordIsNeverOption.bend as Laws

def Laws.plain_word_step(tok, args, up, subs, path, bs, pos, seen, h_dd, h_dash, h_help):
  +rhs = S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen)
  e1 = Equal.sym(Bool, String.eq(tok, "--"), False{}, h_dd)
  %e1 : {S.parse.step.end(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e2 = Equal.sym(Bool, Bool.and(String.eq(tok, "help"), Bool.not(seen)), False{}, h_help)
  %e2 : {S.parse.step.help(_, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e3 = Equal.sym(Bool, String.starts_with(tok, "--"), False{}, Walk.wk.dash(tok, h_dash))
  %e3 : {S.parse.step.kind.go(_, String.starts_with(tok, "-"), tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  e4 = Equal.sym(Bool, String.starts_with(tok, "-"), False{}, h_dash)
  %e4 : {S.parse.step.kind.go(False{}, _, tok, args, up, subs, path, bs, pos, seen) == rhs : S.St}
  {==}

def Laws.dash_word_step(_args, _up, _subs, _path, _bs, _pos, _seen):
  {==}
