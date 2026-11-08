module
import all F3NineDimension318
import all F3RankTwoBases318
import all LiteralKernelGeometricBases318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`F3NineDimension318, `F3RankTwoBases318, `LiteralKernelGeometricBases318]
  for name in #[`F3NineDimension318.finrank_two, `F3RankTwoBases318.pairEquiv,
      `F3RankTwoBases318.familyBasisEquiv, `F3RankTwoBases318.pairBasisEquiv,
      `F3RankTwoBases318.pairBasis_zero, `F3RankTwoBases318.pairBasis_one,
      `F3RankTwoBases318.card_pairs, `F3RankTwoBases318.card_bases,
      `LiteralKernelGeometricBases318.finrank_two,
      `LiteralKernelGeometricBases318.pairBasisEquiv,
      `LiteralKernelGeometricBases318.first_vector,
      `LiteralKernelGeometricBases318.second_vector,
      `LiteralKernelGeometricBases318.card_pairs, `LiteralKernelGeometricBases318.card_bases] do
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
  logInfo m!"GEOMETRIC_KERNEL_BASES_AUDIT_PASS declarations={checked} modules={found}"
