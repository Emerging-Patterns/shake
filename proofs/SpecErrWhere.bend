# proofs of laws/SpecErrWhere.bend
import Base
import ../src/check.bend as K
import ../laws/SpecErrWhere.bend as Laws

def Laws.spec_err_where(err):
  match err:
    case K.RestNotLast{+path, +name}:
      ("rest positional '" ++ name ++ "' is not the last positional", {==})
    case K.SameName{+path, +name}:
      ("two arguments are named '" ++ name ++ "'", {==})
    case K.SameShort{+path, +short}:
      ("two arguments are spelled '-" ++ short ++ "'", {==})
    case K.SameLong{+path, +long}:
      ("two arguments are spelled '--" ++ long ++ "'", {==})
    case K.SameSub{+path, +name}:
      ("two subcommands are named '" ++ name ++ "'", {==})
    case K.HelpSub{+path}:
      ("a subcommand is named 'help', which `parse` keeps for help", {==})
    case K.DefaultNotChoice{+path, +name, +value}:
      ("the default '" ++ value ++ "' of '" ++ name ++ "' is not one of its choices", {==})
    case K.RequiredAfterOptional{+path, +name}:
      ("required positional '" ++ name ++ "' follows an optional one", {==})
