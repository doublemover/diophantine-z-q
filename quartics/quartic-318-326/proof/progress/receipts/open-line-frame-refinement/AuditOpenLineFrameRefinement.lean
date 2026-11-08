module
import all OpenLineFrameRefinement318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`OpenLineFrameRefinement318]
  for name in #[`OpenLineFrameRefinement318.fromOver,`OpenLineFrameRefinement318.over_fromOver,`OpenLineFrameRefinement318.overRestriction,`OpenLineFrameRefinement318.frame,`OpenLineFrameRefinement318.coordinates,`OpenLineFrameRefinement318.refinedFrames,`OpenLineFrameRefinement318.extracted_refine] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"OPEN_LINE_FRAME_REFINEMENT_AUDIT_PASS declarations={checked} modules={found}"
