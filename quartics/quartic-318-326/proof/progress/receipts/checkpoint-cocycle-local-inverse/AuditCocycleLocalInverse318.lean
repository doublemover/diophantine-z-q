module
import all CocycleLocalCoefficients318
import all CocycleOverlapCoordinates318
import all CocycleTwistedCoordinates318
import all CocycleLocalFamily318
import all CocycleLocalLift318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CocycleLocalCoefficients318, `CocycleOverlapCoordinates318,
    `CocycleTwistedCoordinates318, `CocycleLocalFamily318, `CocycleLocalLift318]
  for n in #[`CocycleLocalCoefficients318.localMap,
      `CocycleOverlapCoordinates318.left_coordinate,
      `CocycleTwistedCoordinates318.right_coordinate,
      `CocycleLocalFamily318.compatible, `CocycleLocalFamily318.diagonal_iso,
      `CocycleLocalLift318.localLift, `CocycleLocalLift318.localLift_coefficient,
      `CocycleLocalLift318.restricted_hom_ext] do
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
  logInfo m!"COCYCLE_LOCAL_INVERSE_AUDIT_PASS declarations={count} modules={found}"
