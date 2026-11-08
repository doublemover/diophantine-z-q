module
import all FiniteFlatGenericRank318
import all CompletedCharacterRank318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FiniteFlatGenericRank318, `CompletedCharacterRank318]
  for name in #[`FiniteFlatGenericRank318.affine_rank_eq_fraction_degree,
      `FiniteFlatGenericRank318.finrank_eq_generic_degree,
      `CompletedCharacterRank318.completedMap_rank_eight,
      `CompletedCharacterRank318.finite_flat_rank_eight_surjective] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"FINITE_FLAT_GENERIC_RANK_AUDIT_PASS declarations={checked} modules={found}"
