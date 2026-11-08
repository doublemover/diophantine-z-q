module
import all LocalFrameSectionDetection318
import all IntegralLocalFrameDetection318
import all ContactGlobalSectionDetection318
import all FifthOverlapCoordinates318
import all FifthOverlapDifferentialEquation318
import all FifthActualDifferential318
import all FifthActualDifferentialRestriction318
import all FifthInvariantScalar318
import all FifthGlobalPullbackNormalization318
import all FiveActualPullbacksIndependent318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LocalFrameSectionDetection318,`IntegralLocalFrameDetection318,`ContactGlobalSectionDetection318,`FifthOverlapCoordinates318,`FifthOverlapDifferentialEquation318,`FifthActualDifferential318,`FifthActualDifferentialRestriction318,`FifthInvariantScalar318,`FifthGlobalPullbackNormalization318,`FiveActualPullbacksIndependent318]
  for name in #[`LocalFrameSectionDetection318.image_injective,`IntegralLocalFrameDetection318.chart_eq,`ContactGlobalSectionDetection318.restrict_injective,`FifthOverlapCoordinates318.x_relation,`FifthOverlapCoordinates318.y_relation,`FifthOverlapDifferentialEquation318.normalized_equation,`FifthActualDifferential318.differential,`FifthActualDifferential318.on_common,`FifthActualDifferentialRestriction318.restrict,`FifthInvariantScalar318.scale_identity,`FifthInvariantScalar318.form_eq,`FifthGlobalPullbackNormalization318.global_eq,`FiveActualPullbacksIndependent318.independent,`FiveActualPullbacksIndependent318.fifth_nonzero] do
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
  logInfo m!"FIFTH_INVARIANT_PULLBACK_AUDIT_PASS declarations={checked} modules={found}"
