module
import all LineSheafClass318
import all FifthLineClassNorm318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineSheafClass318,`FifthLineClassNorm318]
  for n in #[`LineSheafClass318.Line,`LineSheafClass318.lineSetoid,
      `LineSheafClass318.classOf_eq_iff,`FifthLineClassNorm318.line,
      `FifthLineClassNorm318.iso,`FifthLineClassNorm318.respects,
      `FifthLineClassNorm318.norm,`FifthLineClassNorm318.norm_classOf,
      `FifthLineClassNorm318.presentation_independent,
      `FifthLineClassNorm318.hom_inv,`FifthLineClassNorm318.inv_hom] do
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
  logInfo m!"LINE_CLASS_NORM_AUDIT_PASS declarations={count} modules={found}"
