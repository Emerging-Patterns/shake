# bolt.bend: how bolt lints this repo. Every rule is an error: the gate must
# see no errors.
# See bolt/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a pure def named by no quantified law. That rule is `coverage` (L001). A
# def no law applies to (IO, a builder, a type alias, proof machinery, the
# example program) says so with `# noqa: L001 <why>` on its def line.
def laws() -> String:
  "error"

# a law with no binder
def closed() -> String:
  "error"

# an @unsafe def a law file reaches
def unsafe() -> String:
  "error"

# SPEC.md's rows and the laws' tags agree
def trace() -> String:
  "error"
