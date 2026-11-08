module
import all F3FrameCoefficients318
import all KernelFrameChangeCoordinates318
import all KernelFrameChangeFamily318
import all KernelFrameChangeEquivariance318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`F3FrameCoefficients318,`KernelFrameChangeCoordinates318,`KernelFrameChangeFamily318,`KernelFrameChangeEquivariance318]
  for name in #[`F3FrameCoefficients318.change_coordinates,`KernelFrameChangeCoordinates318.combination_value,`KernelFrameChangeFamily318.iso,`KernelFrameChangeFamily318.section_change,`KernelFrameChangeFamily318.section_inverse_coordinates,`KernelFrameChangeEquivariance318.equivariant,`KernelFrameChangeEquivariance318.iso_hom,`KernelFrameChangeEquivariance318.original_point_fixed] do
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
  unless found == 4 do throwError "Expected four modules, found {found}"
  logInfo m!"KERNEL_FRAME_EQUIVARIANCE_AUDIT_PASS declarations={checked} modules={found}"
