module
import all StructuralConstantPullback318
import all ActualQuotientConstantPullback318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`StructuralConstantPullback318, `ActualQuotientConstantPullback318]
  let required := #[`StructuralConstantPullback318.constant, `StructuralConstantPullback318.app_constant,
    `StructuralConstantPullback318.globalSection_constant_smul,
    `ActualQuotientConstantPullback318.sourceConstant, `ActualQuotientConstantPullback318.character_constant,
    `ActualQuotientConstantPullback318.fifth_constant,
    `ActualQuotientConstantPullback318.character_invariant_multiple,
    `ActualQuotientConstantPullback318.fifth_invariant_multiple]
  for n in required do
    unless env.contains n do throwError "Missing required endpoint {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for n in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms n
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {n}"
        count := count + 1
        logInfo m!"AXIOM_CHECK {n}: {axs.toList}"
  unless found == 2 do throwError "Missing target module"
  logInfo m!"STRUCTURAL_CONSTANT_PULLBACK_AUDIT_PASS declarations={count} modules={found}"
