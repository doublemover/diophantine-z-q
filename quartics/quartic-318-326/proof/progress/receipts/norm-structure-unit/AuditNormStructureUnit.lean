module
import all StructureLineFrames318
import all UnitCocycleOne318
import all StructureLineCocycleIso318
import all FifthNormUnit318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`StructureLineFrames318, `UnitCocycleOne318, `StructureLineCocycleIso318, `FifthNormUnit318]
  for name in #[`StructureLineFrames318.coordinates, `StructureLineFrames318.transition_one, `StructureLineFrames318.inverseImage_transition_one, `UnitCocycleOne318.map_one, `StructureLineCocycleIso318.iso, `StructureLineCocycleIso318.hom_coefficient, `FifthNormUnit318.norm_cocycle_eq, `FifthNormUnit318.fixedIso, `FifthNormUnit318.chosenIso, `FifthNormUnit318.chosen_hom_inv, `FifthNormUnit318.chosen_inv_hom] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"NORM_STRUCTURE_UNIT_AUDIT_PASS declarations={checked} modules={found}"
