# shake/check: the line a test prints, pass or fail
import Base

# `ok name` or `FAIL name: got ..., want ...`
def say(ok: Bool, name: String, got: String, want: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got ++ ", want " ++ want)

# passes when two strings are equal
def eq_str(name: String, +got: String, +want: String) -> IO(Unit):
  say(String.eq(got, want), name, got, want)
