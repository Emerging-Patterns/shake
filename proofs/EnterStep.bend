# proofs of laws/EnterStep.bend
import Base
import ../src/cli.bend as S
import ../laws/EnterStep.bend as Laws
import ./lemmas/WalkSteps.bend as M1

# nothing blocking: the subcommand is entered
def enter.none(
  +pos: List<&2, S.Arg>,
  +name: String,
  +about: String,
  +next: List<&2, S.Arg>,
  +kids: List<&2, S.Sub>,
  +args: List<&2, S.Arg>,
  +up: List<&2, S.Level>,
  +subs: List<&2, S.Sub>,
  +path: List<&2, String>,
  +bs: List<&2, S.Bind>,
  +seen: Bool,
  h_req: {S.parse.first_req(pos) == None{} : Maybe<&2, String>}
) -> {S.parse.enter_or(S.parse.first_req(pos), S.Sub{name, about, next, kids}, args, up, subs, path, bs, pos, False{},
      seen)
    == S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
      False{}, False{}} : S.St}:
  er = Equal.sym(Maybe<&2, String>, S.parse.first_req(pos), None{}, h_req)
  %er : {S.parse.enter_or(_, S.Sub{name, about, next, kids}, args, up, subs, path, bs, pos, False{}, seen)
    == S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
      False{}, False{}} : S.St}
  {==}

def Laws.enter_step(
  spec,
  pre,
  tok,
  args,
  up,
  subs,
  path,
  bs,
  pos,
  seen,
  name,
  about,
  next,
  kids,
  h_at,
  h_dd,
  h_help,
  h_dash,
  h_sub,
  h_req
):
  +st = {S.St{S.Free{}, args, up, subs, path, bs, pos, False{}, seen} : S.St}
  +sub = {S.Sub{name, about, next, kids} : S.Sub}
  +rhs = {S.St{S.Free{}, next, S.Level{args, bs} <> up, kids, List.append(&2, String, path, [name]), [], S.pos_of(next),
    False{}, False{}} : S.St}
  Equal.trans(S.St, S.parse.walk(List.append(&2, String, pre, [tok]), S.parse.start(spec)), S.parse.step(tok, st), rhs,
    M1.kept.stepped(spec, pre, tok, st, h_at),
    Equal.trans(S.St, S.parse.step(tok, st),
      S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen), rhs,
      M1.enter.word(tok, args, up, subs, path, bs, pos, seen, h_dd, h_help, h_dash),
      Equal.trans(S.St, S.parse.word.go(S.find_sub(subs, tok), tok, args, up, subs, path, bs, pos, False{}, seen),
        S.parse.enter_or(S.parse.first_req(pos), sub, args, up, subs, path, bs, pos, False{}, seen), rhs,
        M1.enter.go(tok, args, up, subs, path, bs, pos, seen, sub, h_sub),
        enter.none(pos, name, about, next, kids, args, up, subs, path, bs, seen, h_req))))
