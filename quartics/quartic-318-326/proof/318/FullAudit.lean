module
import all Current318FinalBridge
import all Current318FinalExactDegree
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModules : Array Name := #[`QuarticOptimization, `SparseQuartic, `CircuitReplay, `ExactDegree, `AffineAnchor, `AnchorValueShear, `Current318FinalPolynomial, `Raw318FinalReplayData, `Raw318FinalReplayStep0, `Raw318FinalReplayStep1, `Raw318FinalReplayStep2, `Raw318FinalReplayStep3, `Raw318FinalReplayStep4, `Raw318FinalReplayStep5, `Raw318FinalReplayStep6, `Raw318FinalReplay, `Current318FinalBridge, `Current318FinalExactDegree]
  let mut checked : Nat := 0
  let mut found : Array Name := #[]
  for idx in [:env.header.modules.size] do
    let modName := env.header.modules[idx]!.module
    if projectModules.contains modName then
      found := found.push modName
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name} from {modName}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  unless found.size == projectModules.size do
    throwError "Missing modules: expected {projectModules}, found {found}"
  logInfo m!"FULL_AXIOM_AUDIT_PASS declarations={checked} modules={found.size}"
