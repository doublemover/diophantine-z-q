module
import all EtaleSectionTrivialization318
import all KernelUniversalFrame318
import all KernelUniversalGeometricBasis318
import all KernelUniversalTrivialization318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`EtaleSectionTrivialization318, `KernelUniversalFrame318,
    `KernelUniversalGeometricBasis318, `KernelUniversalTrivialization318]
  for name in #[`EtaleSectionTrivialization318.section_open,
      `EtaleSectionTrivialization318.disjoint, `EtaleSectionTrivialization318.covers,
      `EtaleSectionTrivialization318.iso, `EtaleSectionTrivialization318.component,
      `KernelUniversalFrame318.pointEquiv, `KernelUniversalFrame318.value_coordinates,
      `KernelUniversalGeometricBasis318.coordinates, `KernelUniversalGeometricBasis318.all_geometric,
      `KernelUniversalTrivialization318.iso, `KernelUniversalTrivialization318.component_original,
      `KernelUniversalTrivialization318.over_frame, `KernelUniversalTrivialization318.first_standard,
      `KernelUniversalTrivialization318.second_standard, `KernelUniversalTrivialization318.zero_standard,
      `KernelUniversalTrivialization318.addition, `KernelUniversalTrivialization318.cover] do
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
  logInfo m!"UNIVERSAL_KERNEL_BASIS_AUDIT_PASS declarations={checked} modules={found}"
