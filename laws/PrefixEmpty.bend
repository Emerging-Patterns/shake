import Base

# LAW: every string starts with the empty string (a lemma)
law prefix_empty:
  for ss: String
  {String.starts_with(ss, "") == True{} : Bool}
