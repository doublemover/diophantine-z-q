module
import all OpenClutchedLine318
import all ModuleOpenIsoCriterion318
import all OpenClutchedTrivialization318
import all FifthNormClutchedLine318
import all FifthNormLineTrivialization318
import all ClutchedGaugeMultiplication318
import all ClutchedGaugeIso318
import all OpenClutchedGauge318
import all FifthNormLineGauge318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`OpenClutchedLine318, `ModuleOpenIsoCriterion318, `OpenClutchedTrivialization318, `FifthNormClutchedLine318, `FifthNormLineTrivialization318, `ClutchedGaugeMultiplication318, `ClutchedGaugeIso318, `OpenClutchedGauge318, `FifthNormLineGauge318]
  for name in #[`OpenClutchedLine318.firstFrame, `OpenClutchedLine318.secondFrame, `ModuleOpenIsoCriterion318.of_restrictions, `OpenClutchedTrivialization318.iso, `FifthNormClutchedLine318.sourceLine, `FifthNormClutchedLine318.normLine, `FifthNormClutchedLine318.source_cover, `FifthNormClutchedLine318.target_transition_value, `FifthNormLineTrivialization318.iso, `ClutchedGaugeIso318.map_isIso, `OpenClutchedGauge318.iso, `OpenClutchedGauge318.first_hom, `OpenClutchedGauge318.second_hom, `FifthNormLineGauge318.iso, `FifthNormLineGauge318.gaugeEquivalent, `FifthNormLineGauge318.pullback_line] do
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
  logInfo m!"FIFTH_NORM_CLUTCHED_LINE_AUDIT_PASS declarations={checked} modules={found}"
