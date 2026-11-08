module
import all AffineModuleBasisFrame318
import all LocalizedModuleSheafFrame318
import all FiniteTargetSheafFrame318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`AffineModuleBasisFrame318, `LocalizedModuleSheafFrame318, `FiniteTargetSheafFrame318]
  for name in #[`AffineModuleBasisFrame318.frame, `LocalizedModuleSheafFrame318.equiv, `LocalizedModuleSheafFrame318.equiv_mk_one, `LocalizedModuleSheafFrame318.equiv_left_inverse, `LocalizedModuleSheafFrame318.equiv_right_inverse, `FiniteTargetSheafFrame318.openFrame, `FiniteTargetSheafFrame318.unitFrame, `FiniteTargetSheafFrame318.exists_frame] do
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
  logInfo m!"LOCALIZED_MODULE_SHEAF_FRAME_AUDIT_PASS declarations={checked} modules={found}"
