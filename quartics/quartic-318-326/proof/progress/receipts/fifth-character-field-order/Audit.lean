module
import all FifthCharacterPolynomial318
import all FifthCharacterField318
import all FifthCharacterOrder318
import all FifthCharacterSource318
import all FifthCharacterReciprocal318
import all FifthCharacterDistinct318
import all FifthReciprocalCoordinates318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthCharacterPolynomial318, `FifthCharacterField318, `FifthCharacterOrder318, `FifthCharacterSource318, `FifthCharacterReciprocal318, `FifthCharacterDistinct318, `FifthReciprocalCoordinates318]
  for name in #[`FifthCharacterPolynomial318.full_product, `FifthCharacterField318.degree_two, `FifthCharacterField318.relative_degree_eight, `FifthCharacterField318.actual_fixed_field, `FifthCharacterField318.sign_mem_fixing_iff, `FifthCharacterField318.fixing_subgroup_card, `FifthCharacterOrder318.embedding_root, `FifthCharacterOrder318.actual_fractionField, `FifthCharacterSource318.toSource_embedding, `FifthCharacterSource318.toSource_injective, `FifthCharacterSource318.toSource_finite, `FifthCharacterSource318.source_root_embedding, `FifthCharacterReciprocal318.equiv, `FifthCharacterReciprocal318.tensorEquiv, `FifthCharacterDistinct318.field_ne_complement, `FifthReciprocalCoordinates318.equiv_root, `FifthReciprocalCoordinates318.equiv_parameter, `FifthReciprocalCoordinates318.inverse_root, `FifthReciprocalCoordinates318.quartic_localization, `FifthReciprocalCoordinates318.cubic_localization] do
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
  logInfo m!"FIFTH_CHARACTER_AUDIT_PASS declarations={checked} modules={found}"
