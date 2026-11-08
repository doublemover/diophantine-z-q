module
import all IntegralFieldNorm318
import all FifthGenericNorm318
import all AffineDominantNorm318
import all FifthChartNorm318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`IntegralFieldNorm318, `FifthGenericNorm318, `AffineDominantNorm318, `FifthChartNorm318]
  for name in #[`IntegralFieldNorm318.norm_embedding, `IntegralFieldNorm318.norm_algebraMap, `IntegralFieldNorm318.unique, `FifthGenericNorm318.norm_pullback, `FifthGenericNorm318.original_norm_product, `AffineDominantNorm318.embedding, `AffineDominantNorm318.pullback, `AffineDominantNorm318.unique, `FifthChartNorm318.original_generic_norm, `FifthChartNorm318.norm_pullback, `FifthChartNorm318.norm_unit] do
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
  logInfo m!"FIFTH_REGULAR_NORM_AUDIT_PASS declarations={checked} modules={found}"
