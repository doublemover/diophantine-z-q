module
import all FrameUnitMultiple318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`FrameUnitMultiple318.multiple,`FrameUnitMultiple318.of_factorization] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not a proposition: {name}"
  let mut n:Nat:=0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module==`FrameUnitMultiple318 then
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless n==2 do throwError "Expected two declarations, found {n}"
  logInfo m!"FRAME_UNIT_MULTIPLE_AUDIT_PASS declarations={n} modules=1"
