module
import all FiniteLocalRankOne318
import all RankOneTargetNeighborhood318
import all FifthRankOneModuleNeighborhood318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FiniteLocalRankOne318, `RankOneTargetNeighborhood318, `FifthRankOneModuleNeighborhood318]
  for name in #[`FiniteLocalRankOne318.finite_maximal, `FiniteLocalRankOne318.exists_basis, `RankOneTargetNeighborhood318.exists_basis, `FifthRankOneModuleNeighborhood318.finite, `FifthRankOneModuleNeighborhood318.original_preimage, `FifthRankOneModuleNeighborhood318.exists_basis] do
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
  logInfo m!"FIFTH_RANK_ONE_NEIGHBORHOOD_AUDIT_PASS declarations={checked} modules={found}"
