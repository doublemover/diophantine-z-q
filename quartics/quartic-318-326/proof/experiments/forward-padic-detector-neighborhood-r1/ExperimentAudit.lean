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
import all NormalizingRadicals318
import all NormalizedPointSigns318
import all NormalizationInjection318
import all NormalizedGeneratorIndependence318
import all NormalizationRealEmbedding318
import all RealOvalNormalization318
import all NormalizedOvalIndependence318
import all OvalInvariantClock318
import all OvalFlowAddition318
import all OvalAddCircle318
import all TorusCharacterDensity318
import all ActualPairDensity318
import all NormalizedPolePoints318
import all CompressedChartDomains318
import all PadeRatioWitness318
import all ActualPadeRatios318
import all DetectorGateWitness318
import all MonotheticComponentSteps318
import all MixedCRTComponentSelection318
import all ActualMixedCRTPrefix318
import all DenseOrbitCRTPrefix318
import all UnconditionalRealCRTPrefix318
import all Source107CRTWitness318
import all ContactWeightWitness318
import all ContactWeightLimits318
import all ContactChainWitness318
import all PoleInputWitness318
import all ContactChainLimits318
import all PoleInputFamily318
import all ContactChainReal318
import all UniformPoleDomain318
import all PoleCertificateFill318
import all UniformPoleFamilies318
import all RealDetectorRatios318
import all RealDetectorCoefficients318
import all RealPadeSourceBridge318
import all RealDetectorSourceBridge318
import all RealDetectorContinuity318
import all CompactDetectorRegion318
import all PreparedPoleCRTWitness318
import all FixedDetectorScales318
import all ScaledContactWeights318
import all ScaledDetectorChain318
import all ActualDetectorFold318
import all ActualDetectorTrace318
import all ActualDetectorPairDepth318
import all DetectorPrimeProduct318
import all DetectorDenominatorPreparation318
import all DetectorSmallPrimePreparation318
import all UniformScaledPoleDomain318
import all ChainInputInvariance318
import all ThreeDetectorPrePole318
import all ThreePoleCertificates318
import all ThreeDetectorUniformFamily318
import all ThreeDetectorCRTWitness318
import all ActualScalarRoot318
import all ScalarForwardWitness318
import all ScalarPoleRealDomain318
import all ScalarActualInputs318
import all ScalarCompleteSource318
import all PreparedIntegerSource318
import all TwoTwistPointRealization318
import all DetectorWeightPreparation318
import all DetectorPreparedThresholds318
import all ScalarPolePreparation318
import all ScalarPackedLocalUnit318
import all ScalarSmallPrimePreparation318
import all ScalarLocalSquares318
import all PreparedTwistSource318
import all ScalarTranslatedIndex318
import all ScalarIndexValuations318
import all ScalarHalfTraceDepth318
import all ScalarTwoThreePreparation318
import all ScalarPreparedCongruence318
import all PreparedTwoThreeSource318
import all ScalarPreparedResidues318
import all FixedArithmeticLabels318
import all PreparedLucasSource318
import all FixedAnchorNormDepths318
import all ActualAnchorRatio318
import all PreparedAnchorLabels318
import all AnchorLocalSquareProduction318
import all ActualLocalAnchorWitness318
import all PhysicalAnchorFromHomogeneous318
import all PreparedAnchorSource318
import all FiniteAnchorIsotropy318
import all PadicAnchorUniversality318
import all ActualAnchorAllPlaces318
import all PreparedAllPlaceSource318
import all ThreeDetectorArithmetic318
import all PadicDetectorCoefficients318
import all PadicDetectorUniformPreparation318
import all Source150CRTWitness318
import all SourcePadicDetectorRegion318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`CoherentSecantPolynomial318,`RealQuarticAssociativityPolynomial318,`CompressedAnchorWitness318,`ReciprocalChartWitness318,`RealGuardWitness318,`RealGuardTrace318,`CoherentMultipleCharts318,`CoherentOrbit318,`AnalyticGuardAvoidance318,`CompactGuardProgression318,`CoherentMultiplePrefix318,`CoherentSecant318,`CoherentRootSign318,`CoherentAdditionU318,`CoherentAdditionV318,`RealQuarticAmbient318,`RealQuarticOvalCover318,`RealQuarticSumU318,`RealQuarticSumAnalytic318,`RealQuarticAssociativity318,`RealQuarticGroup318,`RealQuarticTopologicalGroup318,`RealCoherentOrbit318,`ActualCyclicClosure318,`RealGuardAmbient318,`ActualCyclicGuards318,`ActualCyclicProgressions318,`CyclicPrefixWitness318,`GeneratorScalarProgression318,`NormalizingRadicals318,`NormalizedPointSigns318,`NormalizationInjection318,`NormalizedGeneratorIndependence318,`NormalizationRealEmbedding318,`RealOvalNormalization318,`NormalizedOvalIndependence318,`OvalInvariantClock318,`OvalFlowAddition318,`OvalAddCircle318,`TorusCharacterDensity318,`ActualPairDensity318,`NormalizedPolePoints318,`CompressedChartDomains318,`PadeRatioWitness318,`ActualPadeRatios318,`DetectorGateWitness318,`MonotheticComponentSteps318,`MixedCRTComponentSelection318,`ActualMixedCRTPrefix318,`DenseOrbitCRTPrefix318,`UnconditionalRealCRTPrefix318,`Source107CRTWitness318,`ContactWeightWitness318,`ContactWeightLimits318,`ContactChainWitness318,`PoleInputWitness318,`ContactChainLimits318,`PoleInputFamily318,`ContactChainReal318,`UniformPoleDomain318,`PoleCertificateFill318,`UniformPoleFamilies318,`RealDetectorRatios318,`RealDetectorCoefficients318,`RealPadeSourceBridge318,`RealDetectorSourceBridge318,`RealDetectorContinuity318,`CompactDetectorRegion318,`PreparedPoleCRTWitness318,`FixedDetectorScales318,`ScaledContactWeights318,`ScaledDetectorChain318,`ActualDetectorFold318,`ActualDetectorTrace318,`ActualDetectorPairDepth318,`DetectorPrimeProduct318,`DetectorDenominatorPreparation318,`DetectorSmallPrimePreparation318,`UniformScaledPoleDomain318,`ChainInputInvariance318,`ThreeDetectorPrePole318,`ThreePoleCertificates318,`ThreeDetectorUniformFamily318,`ThreeDetectorCRTWitness318,`ActualScalarRoot318,`ScalarForwardWitness318,`ScalarPoleRealDomain318,`ScalarActualInputs318,`ScalarCompleteSource318,`PreparedIntegerSource318,`TwoTwistPointRealization318,`DetectorWeightPreparation318,`DetectorPreparedThresholds318,`ScalarPolePreparation318,`ScalarPackedLocalUnit318,`ScalarSmallPrimePreparation318,`ScalarLocalSquares318,`PreparedTwistSource318,`ScalarTranslatedIndex318,`ScalarIndexValuations318,`ScalarHalfTraceDepth318,`ScalarTwoThreePreparation318,`ScalarPreparedCongruence318,`PreparedTwoThreeSource318,`ScalarPreparedResidues318,`FixedArithmeticLabels318,`PreparedLucasSource318,`FixedAnchorNormDepths318,`ActualAnchorRatio318,`PreparedAnchorLabels318,`AnchorLocalSquareProduction318,`ActualLocalAnchorWitness318,`PhysicalAnchorFromHomogeneous318,`PreparedAnchorSource318,`FiniteAnchorIsotropy318,`PadicAnchorUniversality318,`ActualAnchorAllPlaces318,`PreparedAllPlaceSource318,`ThreeDetectorArithmetic318,`PadicDetectorCoefficients318,`PadicDetectorUniformPreparation318,`Source150CRTWitness318,`SourcePadicDetectorRegion318]
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
