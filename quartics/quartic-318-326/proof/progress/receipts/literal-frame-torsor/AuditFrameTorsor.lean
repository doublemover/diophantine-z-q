module
import all LiteralFrameTorsorMaps318
import all LiteralFrameTorsorGeometric318
import all LiteralFrameTorsor318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LiteralFrameTorsorMaps318,`LiteralFrameTorsorGeometric318,`LiteralFrameTorsor318]
  for name in #[`LiteralFrameTorsorMaps318.graph_projection,`LiteralFrameTorsorMaps318.graph_second,`LiteralFrameTorsorGeometric318.all_geometric,`LiteralFrameTorsor318.iso,`LiteralFrameTorsor318.component_first,`LiteralFrameTorsor318.component_second,`LiteralFrameTorsor318.graph_inverse,`LiteralFrameTorsor318.over_frame,`LiteralFrameTorsor318.cover] do
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
  logInfo m!"FRAME_TORSOR_AUDIT_PASS declarations={checked} modules={found}"
