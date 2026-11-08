module
import all AffineDominantNormRestriction318
import all NormalAffineBasis318
import all FunctionFieldGluing318
import all OpenDominantNormExistence318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`AffineDominantNormRestriction318, `NormalAffineBasis318, `FunctionFieldGluing318, `OpenDominantNormExistence318]
  for name in #[`AffineDominantNormRestriction318.restrict, `NormalAffineBasis318.of_cover, `FunctionFieldGluing318.exists_section, `OpenDominantNormExistence318.exists_value] do
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
  logInfo m!"NORMAL_OPEN_NORM_GLUE_AUDIT_PASS declarations={checked} modules={found}"
