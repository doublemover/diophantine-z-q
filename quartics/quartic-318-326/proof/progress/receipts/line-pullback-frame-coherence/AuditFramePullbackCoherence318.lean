module
import all OpenFrameRestrictionComparison318
import all PullbackPathComposition318
import all PullbackFrameComposition318
import all PullbackChartComposition318
import all PullbackOpenFrameNormalization318
import all OpenFramePullbackRestriction318
import all LinePullbackFrameCoherence318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`OpenFrameRestrictionComparison318,`PullbackPathComposition318,`PullbackFrameComposition318,`PullbackChartComposition318,`PullbackOpenFrameNormalization318,`OpenFramePullbackRestriction318,`LinePullbackFrameCoherence318]
  for n in #[`OpenFrameRestrictionComparison318.frame_eq,`PullbackPathComposition318.assoc,`PullbackFrameComposition318.composition,`PullbackChartComposition318.extend_assoc,`PullbackChartComposition318.restrict_chart,`PullbackChartComposition318.nested,`PullbackOpenFrameNormalization318.restriction_congr,`PullbackOpenFrameNormalization318.chart_formula,`OpenFramePullbackRestriction318.normalized,`LinePullbackFrameCoherence318.frame] do
    unless env.contains n do throwError "Required endpoint missing: {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for n in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms n
        for a in axs do
          unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
            throwError "Forbidden axiom {a} in {n}"
        logInfo m!"AXIOM_CHECK {n}: {axs}"
        count := count+1
  unless found == 7 do throwError "Missing target module"
  logInfo m!"FRAME_PULLBACK_COHERENCE_AUDIT_PASS declarations={count} modules={found}"
