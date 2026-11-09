module
import all ActualQuotientDifferentialLinear318
import all ActualFivePullbackEquivalence318
import all ActualFivePullbackDirectSum318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ActualQuotientDifferentialLinear318,
    `ActualFivePullbackEquivalence318, `ActualFivePullbackDirectSum318]
  for name in #[`ActualQuotientDifferentialLinear318.pullback_frame,
    `ActualFivePullbackEquivalence318.sumPullback_bijective,
    `ActualFivePullbackEquivalence318.equivalence_apply,
    `ActualFivePullbackEquivalence318.inverse_apply,
    `ActualFivePullbackEquivalence318.existsUnique_decomposition,
    `ActualFivePullbackDirectSum318.equivalence_toLinearMap,
    `ActualFivePullbackDirectSum318.equivalence_component,
    `ActualFivePullbackDirectSum318.sumMap_bijective] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do
        throwError "Expected proposition: {name}"
  for name in #[`ActualFivePullbackEquivalence318.equivalence,
    `ActualFivePullbackDirectSum318.equivalence] do
    unless env.contains name do throwError "Missing actual equivalence {name}"
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
  logInfo m!"ACTUAL_FIVE_PULLBACK_EQUIVALENCE_AUDIT_PASS declarations={declarations} modules={found}"
