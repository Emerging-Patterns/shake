# When `suggestion(spec, err)` is `Some{s}`, `err_text(spec, err)` contains
# `s`.
import Base
import ../main.bend as Shake

# LAW: the error text shows the suggestion, when there is one
law err_text_tip:
  for +spec: Shake.Cli
  for +err: Shake.ParseErr
  for +ss: String
  for h_sug: {Shake.suggestion(spec, err) == Some{ss} : Maybe<&2, String>}
  {String.contains(Shake.err_text(spec, err), ss) == True{} : Bool}
