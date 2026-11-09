module
import all ThreeCompactParameter318
import all LiteralThreeCompactParameter318
import all ThreeExceptionalParameter318
import all ActualThreeExceptionalParameter318
import all ActualThreeParameterProper318
import all ActualThreeGlobalParameter318
import all ActualThreeCuspOrbit318
import all ActualThreeCuspHomeomorph318
import all ActualThreeCuspWidths318
import all ActualThreeCuspJ318
import all ActualThreeQParameter318
import all ThreeParameterGrowth318
import all ActualThreeQMeromorphic318
import all ThreeParameterCompositionOrder318
import all ActualThreeQOrders318
import all ActualThreeInfinityUniformizer318
import all ActualThreeCuspAssignment318
import all ActualThreeCuspExhaustion318
import all ActualThreeCuspOverlap318
import all ActualThreeCuspFilling318
import all ActualThreeCuspCompact318
import all ActualThreeFilledQJ318
import all ActualThreeCuspHausdorff318
import all ActualThreeEndOrders318
import all ActualThreeSphereCharts318
import all ActualThreeFilledParameter318
import all HolomorphicDescent318
import all ActualThreeHolomorphicDescent318
import all ActualThreeQuotientHolomorphic318
import all ActualThreeCuspAnalytic318
import all ActualThreeFilledHolomorphic318
import all SphereInversion318
import all SphereCharts318
import all SphereComplexCurve318
import all ActualThreeComplexAtlas318
import all ActualThreeCanonicalAnalytic318
import all ActualThreeBiholomorph318
import all ActualThreeGlobalHolomorphy318
import all ProjectiveLineFieldPoints318
import all ProjectiveLinePointEquiv318
import all ProjectiveLineComplexTopology318
import all ProjectiveLineComplexAtlas318
import all ProjectiveLineBiholomorph318
import all ActualThreeProjectivePoints318
import all ThreeProjectiveJCertificates318
import all ActualThreeJChartConsumer318
import all RationalPairLocalMaps318
import all RationalPairGluing318
import all ThreeAffineJMaps318
import all RationalPairDenominatorEvaluation318
import all ThreeProjectiveJMap318
import all RationalPairNumeratorEvaluation318
import all ThreeProjectiveJPoints318
import all ActualThreeCompactJPoints318
import all ThreeJAnalyticGerms318
import all ThreeJChartHolomorphy318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ThreeCompactParameter318,`LiteralThreeCompactParameter318,`ThreeExceptionalParameter318,`ActualThreeExceptionalParameter318,`ActualThreeParameterProper318,`ActualThreeGlobalParameter318,`ActualThreeCuspOrbit318,`ActualThreeCuspHomeomorph318,`ActualThreeCuspWidths318,`ActualThreeCuspJ318,`ActualThreeQParameter318,`ThreeParameterGrowth318,`ActualThreeQMeromorphic318,`ThreeParameterCompositionOrder318,`ActualThreeQOrders318,`ActualThreeInfinityUniformizer318,`ActualThreeCuspAssignment318,`ActualThreeCuspExhaustion318,`ActualThreeCuspOverlap318,`ActualThreeCuspFilling318,`ActualThreeCuspCompact318,`ActualThreeFilledQJ318,`ActualThreeCuspHausdorff318,`ActualThreeEndOrders318,`ActualThreeSphereCharts318,`ActualThreeFilledParameter318,`HolomorphicDescent318,`ActualThreeHolomorphicDescent318,`ActualThreeQuotientHolomorphic318,`ActualThreeCuspAnalytic318,`ActualThreeFilledHolomorphic318,`SphereInversion318,`SphereCharts318,`SphereComplexCurve318,`ActualThreeComplexAtlas318,`ActualThreeCanonicalAnalytic318,`ActualThreeBiholomorph318,`ActualThreeGlobalHolomorphy318,`ProjectiveLineFieldPoints318,`ProjectiveLinePointEquiv318,`ProjectiveLineComplexTopology318,`ProjectiveLineComplexAtlas318,`ProjectiveLineBiholomorph318,`ActualThreeProjectivePoints318,`ThreeProjectiveJCertificates318,`ActualThreeJChartConsumer318,`RationalPairLocalMaps318,`RationalPairGluing318,`ThreeAffineJMaps318,`RationalPairDenominatorEvaluation318,`ThreeProjectiveJMap318,`RationalPairNumeratorEvaluation318,`ThreeProjectiveJPoints318,`ActualThreeCompactJPoints318,`ThreeJAnalyticGerms318,`ThreeJChartHolomorphy318]
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
