module
import all LineClassInverse318
import all FifthLineClassNormProduct318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineClassInverse318,`FifthLineClassNormProduct318]
  for n in #[`LineClassInverse318.exists_inverse,`LineClassInverse318.inverse,
      `LineClassInverse318.product_inverse,`LineClassInverse318.inverse_product,
      `FifthLineClassNormProduct318.on_representatives,`FifthLineClassNormProduct318.norm_product] do
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
  logInfo m!"CLASS_INVERSE_NORM_PRODUCT_AUDIT_PASS declarations={count} modules={found}"
