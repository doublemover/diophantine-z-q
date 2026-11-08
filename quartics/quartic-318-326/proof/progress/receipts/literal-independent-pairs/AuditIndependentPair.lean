module
import all F3PairIndependence318
import all LiteralKernelPrimitiveOpen318
import all LiteralIndependentPairOpen318
import all LiteralIndependentPairFunctor318
import all IndependentPairNegativeControl318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`F3PairIndependence318,`LiteralKernelPrimitiveOpen318,`LiteralIndependentPairOpen318,`LiteralIndependentPairFunctor318,`IndependentPairNegativeControl318]
  for name in #[`F3PairIndependence318.pair_iff,`LiteralKernelPrimitiveOpen318.residue_zero_iff,`LiteralIndependentPairOpen318.mem_iff_independent,`LiteralIndependentPairOpen318.universal,`LiteralIndependentPairOpen318.inclusion_closed,`LiteralIndependentPairOpen318.zeroLocus_eq_complement,`LiteralIndependentPairFunctor318.equivalence,`LiteralIndependentPairFunctor318.natural,`IndependentPairNegativeControl318.globally_independent,`IndependentPairNegativeControl318.not_fiberwise_independent] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 5 do throwError "Expected five modules, found {found}"
  logInfo m!"INDEPENDENT_PAIR_AUDIT_PASS declarations={checked} modules={found}"
