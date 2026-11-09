module
import all GeometricIntegralConstants318
import all ActualFiveRationalIndependent318
import all ActualSourceRationalConstants318
import all SingleFlipInvariantLine318
import all ActualDifferentialSignLinear318
import all ActualFiveDifferentialSpanning318
import all ActualFiveDifferentialBasis318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`GeometricIntegralConstants318, `ActualFiveRationalIndependent318,
    `ActualSourceRationalConstants318, `SingleFlipInvariantLine318,
    `ActualDifferentialSignLinear318, `ActualFiveDifferentialSpanning318,
    `ActualFiveDifferentialBasis318]
  for name in #[`GeometricIntegralConstants318.integral_is_constant,
    `ActualSourceRationalConstants318.constant_bijective,
    `ActualFiveRationalIndependent318.independent,
    `SingleFlipInvariantLine318.exists_rational_multiple,
    `ActualDifferentialSignLinear318.full_character_of_flips,
    `ActualFiveDifferentialSpanning318.exists_coefficients,
    `ActualFiveDifferentialBasis318.span_eq_top,
    `ActualFiveDifferentialBasis318.basis_apply,
    `ActualFiveDifferentialBasis318.finrank_eq_five] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do
        throwError "Expected proposition: {name}"
  unless env.contains `ActualFiveDifferentialBasis318.basis do
    throwError "Missing actual Basis object"
  let mut declarations : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axioms}"
        declarations := declarations + 1
  unless found == modules.size do
    throwError "Expected {modules.size} modules, found {found}"
  logInfo m!"RECOVERED_FIVE_BASIS_AUDIT_PASS declarations={declarations} modules={found}"
