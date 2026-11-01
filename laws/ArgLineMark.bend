import Base
import ../src/cli.bend as S
import ./defs/ArgumentLists.bend as D1

# LAW: an Arguments line is the positional's usage mark without the space
# before it, padded, then its help text and the extras an Options line has
law arg_line_mark:
  for +nn: String
  for +sh: Maybe<&2, String>
  for +lo: Maybe<&2, String>
  for +kind: S.ArgKind
  for +hp: String
  for +req: Bool
  for +fb: S.Fallback
  for +cs: List<&2, String>
  for +ww: Nat
  {S.help.arg_line(S.Arg{nn, sh, lo, kind, hp, req, fb, cs}, ww)
    == "  " ++ S.help.pad(String.drop(D1.mark(S.Arg{nn, sh, lo, kind, hp, req, fb, cs}), 1n), ww) ++ "  " ++ hp ++
      S.help.extra(S.Arg{nn, sh, lo, kind, hp, req, fb, cs})
    : String}
