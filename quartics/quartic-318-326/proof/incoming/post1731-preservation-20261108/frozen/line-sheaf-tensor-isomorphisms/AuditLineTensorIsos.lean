module
import all UnitCocycleProductLaws318
import all FramedLineCocycleIso318
import all FramedTensorAssociator318
import all FramedTensorCommutor318
import all FramedTensorUnit318
import all LineSheafTensorIsos318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitCocycleProductLaws318,`FramedLineCocycleIso318,`FramedTensorAssociator318,`FramedTensorCommutor318,`FramedTensorUnit318,`LineSheafTensorIsos318]
  for name in #[`UnitCocycleProductLaws318.assoc,`UnitCocycleProductLaws318.comm,`UnitCocycleProductLaws318.one_product,`UnitCocycleProductLaws318.product_one,`FramedLineCocycleIso318.iso,`FramedLineCocycleIso318.coordinate,`FramedLineCocycleIso318.hom_inv,`FramedLineCocycleIso318.inv_hom,`FramedTensorAssociator318.cocycle_eq,`FramedTensorAssociator318.iso,`FramedTensorAssociator318.hom_inv,`FramedTensorAssociator318.inv_hom,`FramedTensorCommutor318.cocycle_eq,`FramedTensorCommutor318.iso,`FramedTensorCommutor318.hom_inv,`FramedTensorCommutor318.inv_hom,`FramedTensorUnit318.unit_cocycle,`FramedTensorUnit318.cocycle_eq,`FramedTensorUnit318.leftIso,`FramedTensorUnit318.rightIso,`FramedTensorUnit318.left_hom_inv,`FramedTensorUnit318.left_inv_hom,`FramedTensorUnit318.right_hom_inv,`FramedTensorUnit318.right_inv_hom,`LineSheafTensorIsos318.triple_cover,`LineSheafTensorIsos318.assoc,`LineSheafTensorIsos318.comm,`LineSheafTensorIsos318.leftUnit,`LineSheafTensorIsos318.rightUnit,`LineSheafTensorIsos318.assoc_hom_inv,`LineSheafTensorIsos318.assoc_inv_hom,`LineSheafTensorIsos318.comm_hom_inv,`LineSheafTensorIsos318.comm_inv_hom,`LineSheafTensorIsos318.left_hom_inv,`LineSheafTensorIsos318.left_inv_hom,`LineSheafTensorIsos318.right_hom_inv,`LineSheafTensorIsos318.right_inv_hom] do
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
  unless found == 6 do throwError "Expected six modules, found {found}"
  logInfo m!"LINE_TENSOR_ISOS_AUDIT_PASS declarations={checked} modules={found}"
