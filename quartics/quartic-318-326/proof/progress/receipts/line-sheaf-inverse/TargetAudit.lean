module
import all UnitCocycleInverse318
import all LineSheafInverse318
import all FramedLineInverse318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`UnitCocycleInverse318,`LineSheafInverse318,`FramedLineInverse318]
  for name in #[`UnitCocycleInverse318.product_inverse,`UnitCocycleInverse318.inverse_product,
      `UnitCocycleInverse318.map_inverse,`LineSheafInverse318.original_inverse_transitions,
      `LineSheafInverse318.right_cocycle_one,`LineSheafInverse318.left_cocycle_one,
      `LineSheafInverse318.locallyFree,`LineSheafInverse318.right_hom_inv,
      `LineSheafInverse318.right_inv_hom,`LineSheafInverse318.left_hom_inv,
      `LineSheafInverse318.left_inv_hom,`FramedLineInverse318.right_hom_inv,
      `FramedLineInverse318.right_inv_hom,`FramedLineInverse318.left_hom_inv,
      `FramedLineInverse318.left_inv_hom] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Endpoint not proposition: {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==3 do throwError "Expected three modules, found {found}"
  logInfo m!"LINE_INVERSE_AUDIT_PASS declarations={n} modules={found}"
