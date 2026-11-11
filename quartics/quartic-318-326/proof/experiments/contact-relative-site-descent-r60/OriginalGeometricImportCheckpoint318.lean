module
public import AffineSectionConjugation318
public import Lean.Elab.BuiltinEvalCommand
public section
set_option stderrAsMessages false
run_cmd Lean.Elab.Command.liftIO do
  let out ← IO.getStderr
  out.putStrLn "[OriginalGeometricEdge probe] SAME imports loaded; diagnostic command executes"
  out.flush
