# proofs of laws/FailureIsFinal.bend
import Base
import ../src/cli.bend as S
import ../laws/FailFrom.bend as L1
import ../laws/FailureIsFinal.bend as Laws
import ./lemmas/FailedWalkThrough.bend as M1

def Laws.fail_stays(spec, ws, more, err, died):
  Equal.trans(Result<&2, &2, S.ParseErr, S.Matched>,
    S.version.res(spec, S.parse.finish(S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec)))),
    S.version.res(spec, Fail{err}),
    S.version.res(spec, S.parse.finish(S.parse.walk(ws, S.parse.start(spec)))),
    Equal.cong(Result<&2, &2, S.ParseErr, S.Matched>, Result<&2, &2, S.ParseErr, S.Matched>,
      xx => S.version.res(spec, xx),
      S.parse.finish(S.parse.walk(List.append(&2, String, ws, more), S.parse.start(spec))),
      Fail{err}, M1.fs.raw(spec, ws, more, err, died)),
    Equal.cong(Result<&2, &2, S.ParseErr, S.Matched>, Result<&2, &2, S.ParseErr, S.Matched>,
      xx => S.version.res(spec, xx), Fail{err}, S.parse.finish(S.parse.walk(ws, S.parse.start(spec))),
      Equal.sym(Result<&2, &2, S.ParseErr, S.Matched>, S.parse.finish(S.parse.walk(ws, S.parse.start(spec))), Fail{err},
        L1.fail_from(S.parse.walk(ws, S.parse.start(spec)), [], err, died))))
