module
import all CocycleTensorIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`CocycleTensorIso318.frames,`CocycleTensorIso318.tensor_cocycle,`CocycleTensorIso318.iso,`CocycleTensorIso318.hom_inv,`CocycleTensorIso318.inv_hom] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module == `CocycleTensorIso318 then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"COCYCLE_TENSOR_CORE_AUDIT_PASS declarations={checked} modules={found}"
