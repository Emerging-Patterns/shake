import Base

# LAW: dropping nothing from a string leaves it (a lemma)
law drop_zero:
  for ss: String
  {String.drop(ss, 0n) == ss : String}
