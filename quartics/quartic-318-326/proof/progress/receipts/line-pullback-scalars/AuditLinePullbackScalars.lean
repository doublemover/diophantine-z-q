module
import all LinePullbackFrameScalar318
import all LinePullbackUnitScalar318
import all LineFrameTopScalar318
import all LinePullbackOriginalScalar318
import all LinePullbackTransitionScalar318
import all LinePullbackCocycleReduction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LinePullbackFrameScalar318, `LinePullbackUnitScalar318, `LineFrameTopScalar318, `LinePullbackOriginalScalar318, `LinePullbackTransitionScalar318, `LinePullbackCocycleReduction318]
  for name in #[`LinePullbackFrameScalar318.relation, `LinePullbackUnitScalar318.unit, `LineFrameTopScalar318.scalar, `LinePullbackOriginalScalar318.scalar, `LinePullbackTransitionScalar318.of_restriction, `LinePullbackCocycleReduction318.cocycle] do
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
  logInfo m!"LINE_PULLBACK_SCALARS_AUDIT_PASS declarations={checked} modules={found}"
