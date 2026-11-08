module
import all CompletedCharacterLineClassNorm318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`CompletedCharacterLineClassNorm318.respects,
      `CompletedCharacterLineClassNorm318.norm_classOf,
      `CompletedCharacterLineClassNorm318.presentation_independent,
      `CompletedCharacterLineClassNorm318.eq_of_source_class_eq] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not a proposition: {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module==`CompletedCharacterLineClassNorm318 then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax==``propext || ax==``Classical.choice || ax==``Quot.sound do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==1 do throwError "Expected one module, found {found}"
  logInfo m!"CHARACTER_CLASS_NORM_AUDIT_PASS declarations={n} modules={found}"
