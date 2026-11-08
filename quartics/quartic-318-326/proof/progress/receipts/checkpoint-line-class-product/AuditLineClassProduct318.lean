module
import all LineSheafTensor318
import all LineSheafUnit318
import all FifthLineClassNormUnit318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineSheafTensor318,`LineSheafUnit318,`FifthLineClassNormUnit318]
  for n in #[`LineSheafTensor318.line,`LineSheafTensor318.congr,
      `LineSheafTensor318.product,`LineSheafTensor318.product_classOf,
      `LineSheafTensor318.presentation_independent,`LineSheafUnit318.line,
      `LineSheafUnit318.eq_unitClass_iff,`FifthLineClassNormUnit318.norm_unit,
      `FifthLineClassNormUnit318.norm_of_trivial] do
    unless env.contains n do throwError "Required endpoint missing: {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing target module"
  logInfo m!"LINE_CLASS_PRODUCT_AUDIT_PASS declarations={count} modules={found}"
