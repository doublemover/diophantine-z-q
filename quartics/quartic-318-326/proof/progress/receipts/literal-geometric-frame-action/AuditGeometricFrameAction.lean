module
import all F3BasisFrameChange318
import all LiteralIndependentSectionAction318
import all LiteralGeometricFrameTransitivity318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`F3BasisFrameChange318,`LiteralIndependentSectionAction318,`LiteralGeometricFrameTransitivity318]
  for name in #[`F3BasisFrameChange318.exists_unique,`LiteralIndependentSectionAction318.map_structure,`LiteralIndependentSectionAction318.frame_action,`LiteralIndependentSectionAction318.frame_injective,`LiteralGeometricFrameTransitivity318.equivariant,`LiteralGeometricFrameTransitivity318.exists_unique] do
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
  logInfo m!"GEOMETRIC_FRAME_ACTION_AUDIT_PASS declarations={checked} modules={found}"
