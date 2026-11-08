module
import all FractionFieldLocalizationDescent318
import all FifthReciprocalFraction318
import all FifthReciprocalFieldCoordinates318
import all FifthShortFraction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FractionFieldLocalizationDescent318, `FifthReciprocalFraction318, `FifthReciprocalFieldCoordinates318, `FifthShortFraction318]
  for name in #[`FractionFieldLocalizationDescent318.of_localization, `FifthReciprocalFraction318.quartic_fractionField, `FifthReciprocalFraction318.cubic_fractionField, `FifthReciprocalFraction318.embedding_injective, `FifthReciprocalFraction318.actual_fractionField, `FifthReciprocalFieldCoordinates318.embedding_u, `FifthReciprocalFieldCoordinates318.embedding_v, `FifthReciprocalFieldCoordinates318.original_root, `FifthShortFraction318.embedding_injective, `FifthShortFraction318.actual_fractionField, `FifthShortFraction318.embedding_x, `FifthShortFraction318.embedding_y] do
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
  logInfo m!"FIFTH_FRACTION_AUDIT_PASS declarations={checked} modules={found}"
