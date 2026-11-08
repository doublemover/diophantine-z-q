module
import all FifthCharacterShortPolynomial318
import all FifthCharacterShortAlgebra318
import all FifthCharacterShortCoordinates318
import all FifthCharacterShortScheme318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthCharacterShortPolynomial318,`FifthCharacterShortAlgebra318,`FifthCharacterShortCoordinates318,`FifthCharacterShortScheme318]
  for name in #[`FifthCharacterShortPolynomial318.changed_reciprocal,`FifthCharacterShortPolynomial318.discriminant_exact,`FifthCharacterShortPolynomial318.discriminant_unit,`FifthCharacterShortAlgebra318.coordinateEquiv,`FifthCharacterShortCoordinates318.coordinate_u,`FifthCharacterShortCoordinates318.coordinate_v,`FifthCharacterShortCoordinates318.inverse_x,`FifthCharacterShortCoordinates318.inverse_y,`FifthCharacterShortScheme318.affineIso,`FifthCharacterShortScheme318.affineIso_over_Q,`FifthCharacterShortScheme318.intoCompleted_over_Q,`FifthCharacterShortScheme318.associative,`FifthCharacterShortScheme318.group,`FifthCharacterShortScheme318.zero_value] do
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
  unless found == 4 do throwError "Expected four modules, found {found}"
  logInfo m!"FIFTH_SHORT_MODEL_AUDIT_PASS declarations={checked} modules={found}"
