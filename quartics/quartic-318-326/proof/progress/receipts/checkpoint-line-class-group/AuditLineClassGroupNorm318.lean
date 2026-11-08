module
import all LineSheafClassGroup318
import all FifthLineClassNormHom318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineSheafClassGroup318,`FifthLineClassNormHom318]
  for n in #[`LineSheafClassGroup318.product_assoc,`LineSheafClassGroup318.product_comm,
      `LineSheafClassGroup318.unit_product,`LineSheafClassGroup318.product_unit,
      `LineSheafClassGroup318.classCommGroup,`LineSheafClassGroup318.classOf_inverse,
      `FifthLineClassNormHom318.norm,`FifthLineClassNormHom318.on_representatives,
      `FifthLineClassNormHom318.maps_inverse,`FifthLineClassNormHom318.maps_power] do
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
  logInfo m!"LINE_CLASS_GROUP_NORM_AUDIT_PASS declarations={count} modules={found}"
