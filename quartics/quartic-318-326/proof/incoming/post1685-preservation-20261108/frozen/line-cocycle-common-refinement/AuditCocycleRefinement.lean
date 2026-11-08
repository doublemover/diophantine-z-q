module
import all UnitCocycleRefinement318
import all InverseImageLineRefinement318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitCocycleRefinement318,`InverseImageLineRefinement318]
  for name in #[`UnitCocycleRefinement318.refine,`UnitCocycleRefinement318.map_refine,`UnitCocycleRefinement318.refine_gauge,`UnitCocycleRefinement318.common_cover,`InverseImageLineRefinement318.leftCocycle,`InverseImageLineRefinement318.rightCocycle,`InverseImageLineRefinement318.unit,`InverseImageLineRefinement318.unit_restrict,`InverseImageLineRefinement318.left_transition,`InverseImageLineRefinement318.right_transition,`InverseImageLineRefinement318.equation,`InverseImageLineRefinement318.gaugeEquivalent] do
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
  unless found == 2 do throwError "Expected two modules, found {found}"
  logInfo m!"COCYCLE_REFINEMENT_AUDIT_PASS declarations={checked} modules={found}"
