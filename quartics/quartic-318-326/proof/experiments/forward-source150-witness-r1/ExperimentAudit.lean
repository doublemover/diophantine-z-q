module
import all CoherentSecantPolynomial318
import all RealQuarticAssociativityPolynomial318
import all CompressedAnchorWitness318
import all ReciprocalChartWitness318
import all RealGuardWitness318
import all RealGuardTrace318
import all CoherentMultipleCharts318
import all CoherentOrbit318
import all AnalyticGuardAvoidance318
import all CompactGuardProgression318
import all CoherentMultiplePrefix318
import all CoherentSecant318
import all CoherentRootSign318
import all CoherentAdditionU318
import all CoherentAdditionV318
import all RealQuarticAmbient318
import all RealQuarticOvalCover318
import all RealQuarticSumU318
import all RealQuarticSumAnalytic318
import all RealQuarticAssociativity318
import all RealQuarticGroup318
import all RealQuarticTopologicalGroup318
import all RealCoherentOrbit318
import all ActualCyclicClosure318
import all RealGuardAmbient318
import all ActualCyclicGuards318
import all ActualCyclicProgressions318
import all CyclicPrefixWitness318
import all GeneratorScalarProgression318
import all MonotheticComponentSteps318
import all CompressedChartDomains318
import all PadeRatioWitness318
import all ActualPadeRatios318
import all DetectorGateWitness318
import all RealOvalNormalization318
import all OvalInvariantClock318
import all OvalFlowAddition318
import all OvalAddCircle318
import all NormalizingRadicals318
import all NormalizedPointSigns318
import all NormalizationInjection318
import all NormalizedGeneratorIndependence318
import all NormalizationRealEmbedding318
import all NormalizedOvalIndependence318
import all TorusCharacterDensity318
import all ActualPairDensity318
import all MixedCRTComponentSelection318
import all ActualMixedCRTPrefix318
import all DenseOrbitCRTPrefix318
import all UnconditionalRealCRTPrefix318
import all Source107CRTWitness318
import all ContactWeightWitness318
import all ContactChainWitness318
import all Source150CRTWitness318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`CoherentSecantPolynomial318,`RealQuarticAssociativityPolynomial318,`CompressedAnchorWitness318,`ReciprocalChartWitness318,`RealGuardWitness318,`RealGuardTrace318,`CoherentMultipleCharts318,`CoherentOrbit318,`AnalyticGuardAvoidance318,`CompactGuardProgression318,`CoherentMultiplePrefix318,`CoherentSecant318,`CoherentRootSign318,`CoherentAdditionU318,`CoherentAdditionV318,`RealQuarticAmbient318,`RealQuarticOvalCover318,`RealQuarticSumU318,`RealQuarticSumAnalytic318,`RealQuarticAssociativity318,`RealQuarticGroup318,`RealQuarticTopologicalGroup318,`RealCoherentOrbit318,`ActualCyclicClosure318,`RealGuardAmbient318,`ActualCyclicGuards318,`ActualCyclicProgressions318,`CyclicPrefixWitness318,`GeneratorScalarProgression318,`MonotheticComponentSteps318,`CompressedChartDomains318,`PadeRatioWitness318,`ActualPadeRatios318,`DetectorGateWitness318,`RealOvalNormalization318,`OvalInvariantClock318,`OvalFlowAddition318,`OvalAddCircle318,`NormalizingRadicals318,`NormalizedPointSigns318,`NormalizationInjection318,`NormalizedGeneratorIndependence318,`NormalizationRealEmbedding318,`NormalizedOvalIndependence318,`TorusCharacterDensity318,`ActualPairDensity318,`MixedCRTComponentSelection318,`ActualMixedCRTPrefix318,`DenseOrbitCRTPrefix318,`UnconditionalRealCRTPrefix318,`Source107CRTWitness318,`ContactWeightWitness318,`ContactChainWitness318,`Source150CRTWitness318]
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
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
