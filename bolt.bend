# bolt.bend: how bolt lints this repo. Every rule is an error except
# `coverage`, which warns until the laws exist, and `trace`, which waits for
# SPEC.md: the gate must see no errors.
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

# a pure def named by no quantified law: advice while the laws of
# docs/rfc/shake-spec.md are pending. That rule is `coverage` (L001). IO,
# which no law can reach, says so with `# noqa: L001` on its def line.
def laws() -> String:
  "warn"

# a law with no binder
def closed() -> String:
  "error"

# an @unsafe def a law file reaches
def unsafe() -> String:
  "error"

# SPEC.md's rows and the laws' tags agree: off until SPEC.md lands (rollout
# phase one in docs/rfc/shake-spec.md), then an error
def trace() -> String:
  "off"
