module
import all LineFrameAdjunction318
import all CocycleReconstructionCriterion318
import all LineFrameChartCoordinates318
import all ClutchedChartSections318
import all LineFrameCoefficientCompatibility318
import all LineFrameCocycleReconstruction318
import all LineFrameReconstructionIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineFrameAdjunction318, `CocycleReconstructionCriterion318, `LineFrameChartCoordinates318, `ClutchedChartSections318, `LineFrameCoefficientCompatibility318, `LineFrameCocycleReconstruction318, `LineFrameReconstructionIso318]
  for name in #[`LineFrameAdjunction318.transpose, `LineFrameChartCoordinates318.coordinate_app, `ClutchedChartSections318.left_apply, `ClutchedChartSections318.right_apply, `LineFrameCoefficientCompatibility318.compatible, `LineFrameCocycleReconstruction318.map_projection, `LineFrameReconstructionIso318.iso, `LineFrameReconstructionIso318.hom_inv, `LineFrameReconstructionIso318.inv_hom, `LineFrameReconstructionIso318.inv_coordinate, `LineFrameReconstructionIso318.original_frame] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"LINE_FRAME_RECONSTRUCTION_AUDIT_PASS declarations={checked} modules={found}"
