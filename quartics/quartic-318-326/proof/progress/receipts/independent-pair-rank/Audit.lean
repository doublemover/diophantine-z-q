module
import all FiniteEtaleGeometricRank318
import all FiniteEtaleRankFromSections318
import all LiteralIndependentPairRank318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FiniteEtaleGeometricRank318, `FiniteEtaleRankFromSections318, `LiteralIndependentPairRank318]
  for name in #[`FiniteEtaleGeometricRank318.card_sections_eq_rank,
      `FiniteEtaleRankFromSections318.rank_eq,
      `LiteralIndependentPairRank318.rank_forty_eight,
      `LiteralIndependentPairRank318.surjective,
      `LiteralIndependentPairRank318.finite_etale_surjective] do
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
  logInfo m!"INDEPENDENT_PAIR_RANK_AUDIT_PASS declarations={checked} modules={found}"
