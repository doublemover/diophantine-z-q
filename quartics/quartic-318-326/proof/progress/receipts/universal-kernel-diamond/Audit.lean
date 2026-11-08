module
import all KernelUniversalDiamond318
import all KernelUniversalDiamondEquivariance318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`KernelUniversalDiamond318, `KernelUniversalDiamondEquivariance318]
  for name in #[`KernelUniversalDiamond318.map_original, `KernelUniversalDiamond318.map_projection,
      `KernelUniversalDiamond318.iso, `KernelUniversalDiamond318.combination_smul,
      `KernelUniversalDiamond318.section_map,
      `KernelUniversalDiamondEquivariance318.coefficientIso,
      `KernelUniversalDiamondEquivariance318.equivariance,
      `KernelUniversalDiamondEquivariance318.negation_equivariance] do
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
  logInfo m!"UNIVERSAL_KERNEL_DIAMOND_AUDIT_PASS declarations={checked} modules={found}"
