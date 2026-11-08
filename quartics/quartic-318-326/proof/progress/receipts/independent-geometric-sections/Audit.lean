module
import all KernelPairSections318
import all IndependentPairSingleton318
import all LiteralIndependentGeometricBases318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`KernelPairSections318, `IndependentPairSingleton318, `LiteralIndependentGeometricBases318]
  for name in #[`KernelPairSections318.equiv, `KernelPairSections318.restrict_val,
      `IndependentPairSingleton318.mem_iff, `IndependentPairSingleton318.equivalence,
      `IndependentPairSingleton318.first_value, `IndependentPairSingleton318.second_value,
      `LiteralIndependentGeometricBases318.basisEquiv,
      `LiteralIndependentGeometricBases318.first_value,
      `LiteralIndependentGeometricBases318.second_value,
      `LiteralIndependentGeometricBases318.card_forty_eight] do
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
  logInfo m!"INDEPENDENT_GEOMETRIC_SECTIONS_AUDIT_PASS declarations={checked} modules={found}"
