module
import all AffinePrincipalLineFrame318
import all FiniteLineTargetNeighborhood318
import all FiniteLineTargetCover318
import all FifthLineTargetCover318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`AffinePrincipalLineFrame318, `FiniteLineTargetNeighborhood318, `FiniteLineTargetCover318, `FifthLineTargetCover318]
  for name in #[`AffinePrincipalLineFrame318.iso_square, `AffinePrincipalLineFrame318.frame, `FiniteLineTargetNeighborhood318.exists_frame, `FiniteLineTargetCover318.exists_affine_frame, `FiniteLineTargetCover318.cover_top, `FiniteLineTargetCover318.preimage_cover_top, `FiniteLineTargetCover318.frame, `FifthLineTargetCover318.cover_top, `FifthLineTargetCover318.frame] do
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
  logInfo m!"FINITE_LINE_TARGET_COVER_AUDIT_PASS declarations={checked} modules={found}"
