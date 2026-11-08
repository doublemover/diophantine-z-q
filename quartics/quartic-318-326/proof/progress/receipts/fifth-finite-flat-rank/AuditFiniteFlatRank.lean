module
import all FifthReciprocalBaseSquare318
import all FifthCompletedFinite318
import all FifthCompletedFlat318
import all FifthCompletedRank318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthReciprocalBaseSquare318, `FifthCompletedFinite318, `FifthCompletedFlat318, `FifthCompletedRank318]
  for name in #[`FifthReciprocalBaseSquare318.reciprocal_ring_square, `FifthCompletedFinite318.over_t, `FifthCompletedFinite318.finite, `FifthCompletedFinite318.target_finite, `FifthCompletedFlat318.finite_flat_surjective, `FifthCompletedRank318.rank_eight, `FifthCompletedRank318.finite_flat_surjective_rank_eight] do
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
  logInfo m!"FIFTH_FINITE_FLAT_RANK_AUDIT_PASS declarations={checked} modules={found}"
