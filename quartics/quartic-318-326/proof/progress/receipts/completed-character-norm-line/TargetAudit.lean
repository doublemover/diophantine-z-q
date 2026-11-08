module
import all FiniteUnitTransferPresentation318
import all FiniteUnitTransferLine318
import all CompletedCharacterNormLine318
import all CompletedCharacterNormTransition318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`FiniteUnitTransferPresentation318,`FiniteUnitTransferLine318,`CompletedCharacterNormLine318,`CompletedCharacterNormTransition318]
  for name in #[`FiniteUnitTransferPresentation318.target_cover,`FiniteUnitTransferPresentation318.source_cover,
      `FiniteUnitTransferPresentation318.source_hom_inv,`FiniteUnitTransferPresentation318.source_inv_hom,
      `FiniteUnitTransferPresentation318.source_coordinate,`FiniteUnitTransferPresentation318.transition,
      `FiniteUnitTransferLine318.frame_hom_inv,`FiniteUnitTransferLine318.frame_inv_hom,
      `FiniteUnitTransferLine318.locallyFree,`FiniteUnitTransferLine318.original_transitions,
      `FiniteUnitTransferLine318.coefficients,`CompletedCharacterNormLine318.cover,
      `CompletedCharacterNormLine318.locallyFree,`CompletedCharacterNormLine318.frame_hom_inv,
      `CompletedCharacterNormLine318.frame_inv_hom,`CompletedCharacterNormLine318.original_target_transitions,
      `CompletedCharacterNormLine318.norm_original_transition,`FiniteUnitTransferPresentation318.original_transition,
      `CompletedCharacterNormTransition318.originalUnit_eq,`CompletedCharacterNormTransition318.original_norm_transition] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Endpoint not proposition: {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==4 do throwError "Expected four modules, found {found}"
  logInfo m!"CHARACTER_NORM_LINE_AUDIT_PASS declarations={n} modules={found}"
