module
import all ChangedKernelProductAlgebra318
import all ChangedKernelProjection318
import all ChangedKernelProductScheme318
import all ChangedFullKernel318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ChangedKernelProductAlgebra318, `ChangedKernelProjection318, `ChangedKernelProductScheme318, `ChangedFullKernel318]
  for name in #[`ChangedKernelProductAlgebra318.equivalence, `ChangedKernelProductAlgebra318.first_projection,
      `ChangedKernelProductAlgebra318.second_projection, `ChangedKernelProjection318.scalarIso_inv_map,
      `ChangedKernelProductScheme318.finite_inv, `ChangedKernelProductScheme318.zero_inv,
      `ChangedFullKernel318.iso, `ChangedFullKernel318.inl_iso_inv, `ChangedFullKernel318.inr_iso_inv] do
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
  logInfo m!"CHANGED_FULL_KERNEL_AUDIT_PASS declarations={checked} modules={found}"
