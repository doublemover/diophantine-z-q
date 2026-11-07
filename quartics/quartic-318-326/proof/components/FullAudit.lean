module
import all QuarticOptimization
import all SparseQuartic
import all CircuitReplay
import all ExactDegree
import all CoupledExponents
import all OddAnchor
import all ScalarJacobi
import all SingleFortyWeight
import all MixedElevenFortyOne
import all SixHelperWeights
import all AffineAnchor
import all AnchorValueShear
import all NestedInput
import all ConcreteQuadraticDomains
import all ReciprocalDeltaLog
import all NormChainValuation
import all NormChainZero
import all NormChainExtraction
import all OddAffineInput
import all ArithmeticSeparation
import all BaseWeightFusion
import all AcyclicWeightLowerBound
import all SharedScaleInverse
import all GreenBoundConstants
import all G8Nonvanishing
import all Height13DeltaLog
import all Height13RealLog
import all OrdinaryPoleNormalization
import all SixHeight13Weights
import all DegenerateDetector
import all ConcreteG8Domain
import all G4Nonvanishing
import all ConcreteG4Domain
import all Height925DeltaLog
import all ThreeHelperPoleNormalization
import all PadeNumeratorNonvanishing
import all PadeDenominatorNonvanishing
import all PadeAccuracy
import all Pade21Domains
import all Pade21Accuracy
import all FiveHeight49Weights
import all DegenerateContacts
import all EvenDeltaValuation
import all ValuationCurveParity
import all ValuationEvenNormChain
import all ValuationNormChainExtraction
import all Height13WeightLowerBound
import all ValuationTraceSelection
import all ConcreteValuationTrace
import all Pade21LocalError
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModules : Array Name := #[`QuarticOptimization, `SparseQuartic, `CircuitReplay, `ExactDegree, `CoupledExponents, `OddAnchor, `ScalarJacobi, `SingleFortyWeight, `MixedElevenFortyOne, `SixHelperWeights, `AffineAnchor, `AnchorValueShear, `NestedInput, `ConcreteQuadraticDomains, `ReciprocalDeltaLog, `NormChainValuation, `NormChainZero, `NormChainExtraction, `OddAffineInput, `ArithmeticSeparation, `BaseWeightFusion, `AcyclicWeightLowerBound, `SharedScaleInverse, `GreenBoundConstants, `G8Nonvanishing, `Height13DeltaLog, `Height13RealLog, `OrdinaryPoleNormalization, `SixHeight13Weights, `DegenerateDetector, `ConcreteG8Domain, `G4Nonvanishing, `ConcreteG4Domain, `Height925DeltaLog, `ThreeHelperPoleNormalization, `PadeNumeratorNonvanishing, `PadeDenominatorNonvanishing, `PadeAccuracy, `Pade21Domains, `Pade21Accuracy, `FiveHeight49Weights, `DegenerateContacts, `EvenDeltaValuation, `ValuationCurveParity, `ValuationEvenNormChain, `ValuationNormChainExtraction, `Height13WeightLowerBound, `ValuationTraceSelection, `ConcreteValuationTrace, `Pade21LocalError]
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
