module
import all OpenDominantNorm318
import all OpenUnitNorm318
import all StructureUnitsSheaf318
import all FifthOpenNorm318
import all FifthSheafNorm318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`OpenDominantNorm318, `OpenUnitNorm318, `StructureUnitsSheaf318, `FifthOpenNorm318, `FifthSheafNorm318]
  for name in #[`OpenDominantNorm318.norm_embedding, `OpenDominantNorm318.restrict, `OpenDominantNorm318.affine_eq, `OpenDominantNorm318.pullback, `OpenUnitNorm318.norm, `StructureUnitsSheaf318.isSheaf, `StructureUnitsSheaf318.norm, `FifthOpenNorm318.pullback, `FifthOpenNorm318.chart_eq, `FifthSheafNorm318.pullback_norm, `FifthSheafNorm318.norm_original_value] do
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
  logInfo m!"FIFTH_OPEN_UNIT_SHEAF_NORM_AUDIT_PASS declarations={checked} modules={found}"
