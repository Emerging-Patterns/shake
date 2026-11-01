# proofs of laws/SuggestionPicksClosestLong.bend
import Base
import ../src/cli.bend as S
import ../src/walk.bend as Walk
import ../laws/DropZero.bend as L1
import ../laws/PrefixEmpty.bend as L2
import ../laws/SuggestionPicksClosestLong.bend as Laws
import ../laws/defs/HelpPages.bend as D1
import ./lemmas/WalkSteps.bend as M1

def Laws.sug_other(spec, err, h_err):
  match err:
    case S.UnknownFlag{at, word}:
      Empty.absurd({S.suggestion(spec, S.UnknownFlag{at, word}) == None{} : Maybe<&2, String>},
        Walk.wk.true_false(h_err))
    case S.Missing{_at, _name}:
      {==}
    case S.NoValue{_at, _name}:
      {==}
    case S.BadValue{_at, _name, _value}:
      {==}
    case S.NeedHelp{_path}:
      {==}
    case S.Unexpected{_at, _arg}:
      {==}
    case S.Repeated{_at, _name}:
      {==}
    case S.NeedVersion{}:
      {==}

def Laws.sug_short(spec, at, word, h_word):
  e1 = Equal.sym(Bool, String.starts_with(word, "--"), False{}, h_word)
  %e1 : {S.sug.word.go(_, spec, at, word) == None{} : Maybe<&2, String>}
  {==}

# the arguments reached down a path are those of the page `help` reaches
def sa.go(
  path: List<&2, String>,
  how: S.How
) -> {S.sug.args.go(path, how) == Laws.how_args(D1.reach(path, how)) : List<&2, S.Arg>}:
  match path:
    case Nil{}:
      match how:
        case S.How{_b, _a, _v, _g, _s, _u}:
          {==}
    case Con{+hh, tt}:
      sa.go(tt, S.help.step(how, hh))

# the arguments of the command at a path are those of its help page
def sa.reach(
  spec: S.Cli,
  path: List<&2, String>
) -> {S.sug.args(spec, path) == Laws.how_args(D1.reach(path, D1.root(spec))) : List<&2, S.Arg>}:
  match spec:
    case S.Cli{+n, a, v, args, subs}:
      sa.go(path, S.How{n, a, v, args, subs, n})

def Laws.sug_long(spec, at, body, name, val, h_cut):
  e1 = Equal.sym(Bool, String.starts_with(body, ""), True{}, L2.prefix_empty(body))
  %e1 : {S.sug.word.go(_, spec, at, "--" ++ body)
    == S.sug.found(S.sug.best(S.sug.cands(Laws.how_args(D1.reach(at, D1.root(spec)))), name))
    : Maybe<&2, String>}
  e2 = Equal.sym(String, String.drop(body, 0n), body, L1.drop_zero(body))
  %e2 : {S.sug.found(S.sug.best(S.sug.cands(S.sug.args(spec, at)), S.sug.typed(S.cut_eq(_))))
    == S.sug.found(S.sug.best(S.sug.cands(Laws.how_args(D1.reach(at, D1.root(spec)))), name))
    : Maybe<&2, String>}
  e3 = Equal.sym(String & Maybe<&2, String>, S.cut_eq(body), (name, val), h_cut)
  %e3 : {S.sug.found(S.sug.best(S.sug.cands(S.sug.args(spec, at)), S.sug.typed(_)))
    == S.sug.found(S.sug.best(S.sug.cands(Laws.how_args(D1.reach(at, D1.root(spec)))), name))
    : Maybe<&2, String>}
  e4 = Equal.sym(List<&2, S.Arg>, S.sug.args(spec, at), Laws.how_args(D1.reach(at, D1.root(spec))),
    sa.reach(spec, at))
  %e4 : {S.sug.found(S.sug.best(S.sug.cands(_), name))
    == S.sug.found(S.sug.best(S.sug.cands(Laws.how_args(D1.reach(at, D1.root(spec)))), name))
    : Maybe<&2, String>}
  {==}

def Laws.sug_found_some(_cc):
  {==}

def Laws.cands_some(_nn, _sh, _ll, _kind, _hp, _req, _fb, _cs, _tt):
  {==}

def Laws.cands_none(_nn, _sh, _kind, _hp, _req, _fb, _cs, _tt):
  {==}

def Laws.sug_close(_typed, _cc):
  {==}

def Laws.best_nil(_typed):
  {==}

def Laws.best_far(cc, tt, typed, h_far):
  e1 = Equal.sym(Bool, S.sug.close(typed, cc), False{}, h_far)
  %e1 : {S.sug.keep(_, typed, cc, S.sug.best(tt, typed)) == S.sug.best(tt, typed) : Maybe<&2, String>}
  {==}

def Laws.best_only(cc, tt, typed, h_close, h_rest):
  e1 = Equal.sym(Bool, S.sug.close(typed, cc), True{}, h_close)
  %e1 : {S.sug.keep(_, typed, cc, S.sug.best(tt, typed)) == Some{cc} : Maybe<&2, String>}
  e2 = Equal.sym(Maybe<&2, String>, S.sug.best(tt, typed), None{}, h_rest)
  %e2 : {S.sug.keep(True{}, typed, cc, _) == Some{cc} : Maybe<&2, String>}
  {==}

def Laws.best_here(cc, tt, typed, ww, h_close, h_rest, h_le):
  e1 = Equal.sym(Bool, S.sug.close(typed, cc), True{}, h_close)
  %e1 : {S.sug.keep(_, typed, cc, S.sug.best(tt, typed)) == Some{cc} : Maybe<&2, String>}
  e2 = Equal.sym(Maybe<&2, String>, S.sug.best(tt, typed), Some{ww}, h_rest)
  %e2 : {S.sug.keep(True{}, typed, cc, _) == Some{cc} : Maybe<&2, String>}
  e3 = Equal.sym(Bool, Nat.is_le(S.osa(typed, cc), S.osa(typed, ww)), True{}, h_le)
  %e3 : {Bool.pick(Maybe<&2, String>, _, Some{cc}, Some{ww}) == Some{cc} : Maybe<&2, String>}
  {==}

def Laws.best_there(cc, tt, typed, ww, h_close, h_rest, h_le):
  e1 = Equal.sym(Bool, S.sug.close(typed, cc), True{}, h_close)
  %e1 : {S.sug.keep(_, typed, cc, S.sug.best(tt, typed)) == Some{ww} : Maybe<&2, String>}
  e2 = Equal.sym(Maybe<&2, String>, S.sug.best(tt, typed), Some{ww}, h_rest)
  %e2 : {S.sug.keep(True{}, typed, cc, _) == Some{ww} : Maybe<&2, String>}
  e3 = Equal.sym(Bool, Nat.is_le(S.osa(typed, cc), S.osa(typed, ww)), False{}, h_le)
  %e3 : {Bool.pick(Maybe<&2, String>, _, Some{cc}, Some{ww}) == Some{ww} : Maybe<&2, String>}
  {==}
