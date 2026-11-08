module
import all InfinityKernelNeighborhoodPolynomial318
import all InfinityKernelNeighborhoodOutput318
import all InfinityKernelNeighborhoodAlgebra318
import all InfinityKernelNeighborhoodOrigin318
import all InfinityKernelNeighborhoodScheme318
import all InfinityKernelNeighborhoodZero318
import all InfinityKernelNeighborhoodTripling318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`InfinityKernelNeighborhoodPolynomial318,`InfinityKernelNeighborhoodOutput318,`InfinityKernelNeighborhoodAlgebra318,`InfinityKernelNeighborhoodOrigin318,`InfinityKernelNeighborhoodScheme318,`InfinityKernelNeighborhoodZero318,`InfinityKernelNeighborhoodTripling318]
  for name in #[`InfinityKernelNeighborhoodPolynomial318.kernel_factor,`InfinityKernelNeighborhoodOutput318.input_zero,`InfinityKernelNeighborhoodAlgebra318.input_zero,`InfinityKernelNeighborhoodOrigin318.denominator_at_zero,`InfinityKernelNeighborhoodOrigin318.origin_denominator,`InfinityKernelNeighborhoodScheme318.doubling,`InfinityKernelNeighborhoodScheme318.intoCurve_open,`InfinityKernelNeighborhoodZero318.scheme_zero,`InfinityKernelNeighborhoodTripling318.scheme_zero,`InfinityKernelNeighborhoodTripling318.originSection_intoCurve] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked + 1
  unless found == 7 do throwError "Expected seven modules, found {found}"
  logInfo m!"INFINITY_NEIGHBORHOOD_AUDIT_PASS declarations={checked} modules={found}"
