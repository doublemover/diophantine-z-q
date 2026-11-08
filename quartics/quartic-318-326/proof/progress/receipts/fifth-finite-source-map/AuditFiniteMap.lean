module
import all FifthQuarticCover318
import all FifthQuarticFinite318
import all FifthQuarticFiniteCoordinates318
import all FifthSourceAffine318
import all FifthQuarticCompatibility318
import all FifthQuarticCompletedMap318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthQuarticCover318, `FifthQuarticFinite318, `FifthQuarticFiniteCoordinates318, `FifthSourceAffine318, `FifthQuarticCompatibility318, `FifthQuarticCompletedMap318]
  for name in #[`FifthQuarticCover318.span_top, `FifthQuarticFinite318.shortMap_field, `FifthQuarticFiniteCoordinates318.x_relation, `FifthQuarticFiniteCoordinates318.y_relation, `FifthSourceAffine318.map_surjective, `FifthQuarticCompatibility318.agreement, `FifthQuarticCompatibility318.compatible, `FifthQuarticCompletedMap318.restriction, `FifthQuarticCompletedMap318.branch_zero, `FifthQuarticCompletedMap318.sourceMap, `FifthQuarticCompletedMap318.source_over_Q] do
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
  logInfo m!"FIFTH_FINITE_MAP_AUDIT_PASS declarations={checked} modules={found}"
