module
import all UnitCocycleProduct318
import all TensorLineLocalFrame318
import all TensorLineFrameCoordinates318
import all TensorLineCocycle318
import all TensorLineCoordinateMaps318
import all CocycleTensorIso318
import all TensorInverseImageCocycle318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitCocycleProduct318,`TensorLineLocalFrame318,`TensorLineFrameCoordinates318,`TensorLineCocycle318,`TensorLineCoordinateMaps318,`CocycleTensorIso318,`TensorInverseImageCocycle318]
  for name in #[`UnitCocycleProduct318.product,`UnitCocycleProduct318.map_product,`TensorLineLocalFrame318.frame,`TensorLineLocalFrame318.hom_inv,`TensorLineLocalFrame318.inv_hom,`TensorLineLocalFrame318.inverse_pure,`TensorLineFrameCoordinates318.inverse_pure,`TensorLineCocycle318.frame_pure,`TensorLineCocycle318.scalar_product,`TensorLineCocycle318.cocycle_eq,`TensorLineCoordinateMaps318.coordinate_pure,`CocycleTensorIso318.iso,`CocycleTensorIso318.hom_inv,`CocycleTensorIso318.inv_hom,`CocycleTensorIso318.hom_coefficient,`CocycleTensorIso318.hom_frame,`CocycleTensorIso318.inv_frame,`CocycleTensorIso318.pure_coefficient,`TensorInverseImageCocycle318.cocycle_eq] do
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
  unless found == 7 do throwError "Expected seven modules, found {found}"
  logInfo m!"COCYCLE_TENSOR_AUDIT_PASS declarations={checked} modules={found}"
