module
import all OpenModuleTransition318
import all OpenModuleChartRecovery318
import all OpenModulePresheaf318
import all OpenModuleSheafGluing318
import all OpenModuleGluedSheaf318
import all OpenSheafTransition318
import all OpenSheafGluing318
import all OpenChartModuleImages318
import all LocalLineGlobalFrames318
import all OpenChartLineEffectivity318
import all OpenSheafRestrictionCompatibility318
import all OpenSchemeTransition318
import all OpenSchemeGluing318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`OpenModuleTransition318,`OpenModuleChartRecovery318,`OpenModulePresheaf318,`OpenModuleSheafGluing318,`OpenModuleGluedSheaf318,`OpenSheafTransition318,`OpenSheafGluing318,`OpenChartModuleImages318,`LocalLineGlobalFrames318,`OpenChartLineEffectivity318,`OpenSheafRestrictionCompatibility318,`OpenSchemeTransition318,`OpenSchemeGluing318]
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
