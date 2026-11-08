module
import all UnitModuleScalar318
import all UnitSourceExt318
import all UnitSheafScalar318
import all OpenLineFrameCoordinates318
import all FrameScalarAlgebra318
import all LineFrameTransitions318
import all LineFrameCocycle318
import all LineFrameGauge318
import all InverseImageLineCocycle318
import all FifthLineExtractedCocycle318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitModuleScalar318,`UnitSourceExt318,`UnitSheafScalar318,`OpenLineFrameCoordinates318,`FrameScalarAlgebra318,`LineFrameTransitions318,`LineFrameCocycle318,`LineFrameGauge318,`InverseImageLineCocycle318,`FifthLineExtractedCocycle318]
  for name in #[`UnitModuleScalar318.unit,`UnitModuleScalar318.value_apply,`UnitModuleScalar318.unique,`UnitSourceExt318.eq_ofTop,`UnitSourceExt318.ext,`UnitSheafScalar318.hom_eq,`UnitSheafScalar318.unit,`UnitSheafScalar318.hom_multiply,`UnitSheafScalar318.inv_multiply,`UnitSheafScalar318.unique,`OpenLineFrameCoordinates318.frame,`OpenLineFrameCoordinates318.natural,`OpenLineFrameCoordinates318.inverse_natural,`FrameScalarAlgebra318.relation,`FrameScalarAlgebra318.unique,`FrameScalarAlgebra318.comp,`FrameScalarAlgebra318.gauge,`LineFrameTransitions318.scalar,`LineFrameTransitions318.relation,`LineFrameTransitions318.unique,`LineFrameTransitions318.restrict,`LineFrameCocycle318.cocycle,`LineFrameCocycle318.relation,`LineFrameGauge318.equation,`LineFrameGauge318.equivalent,`InverseImageLineCocycle318.cocycle,`InverseImageLineCocycle318.gauge_equation,`InverseImageLineCocycle318.gaugeEquivalent,`FifthLineExtractedCocycle318.source,`FifthLineExtractedCocycle318.target,`FifthLineExtractedCocycle318.target_transition] do
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
  unless found == 10 do throwError "Expected ten modules, found {found}"
  logInfo m!"LINE_FRAME_TRANSITIONS_AUDIT_PASS declarations={checked} modules={found}"
