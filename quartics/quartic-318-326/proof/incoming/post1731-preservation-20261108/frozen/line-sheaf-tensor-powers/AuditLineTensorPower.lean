module
import all UnitCocyclePower318
import all FramedLineTensorPower318
import all LineSheafTensorPower318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitCocyclePower318,`FramedLineTensorPower318,`LineSheafTensorPower318]
  for name in #[`UnitCocyclePower318.power,`UnitCocyclePower318.transition,`UnitCocyclePower318.zero,`UnitCocyclePower318.succ,`UnitCocyclePower318.map_power,`FramedLineTensorPower318.object,`FramedLineTensorPower318.object_zero,`FramedLineTensorPower318.object_succ,`FramedLineTensorPower318.frames,`FramedLineTensorPower318.cocycle_eq,`FramedLineTensorPower318.transition,`FramedLineTensorPower318.iso,`FramedLineTensorPower318.hom_inv,`FramedLineTensorPower318.inv_hom,`FramedLineTensorPower318.coefficient,`FramedLineTensorPower318.eighthIso,`LineSheafTensorPower318.line,`LineSheafTensorPower318.zeroIso,`LineSheafTensorPower318.succIso,`LineSheafTensorPower318.classOf_power,`LineSheafTensorPower318.iso,`LineSheafTensorPower318.hom_inv,`LineSheafTensorPower318.inv_hom,`LineSheafTensorPower318.classOf_eighth,`LineSheafTensorPower318.eighthIso] do
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
  unless found == 3 do throwError "Expected three modules, found {found}"
  logInfo m!"LINE_TENSOR_POWER_AUDIT_PASS declarations={checked} modules={found}"
