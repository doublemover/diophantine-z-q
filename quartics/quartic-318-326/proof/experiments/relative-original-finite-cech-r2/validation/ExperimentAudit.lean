module
import all ContactWholeInfinityAlgebra318
import all ContactWholeInfinityScheme318
import all OriginalAffineTestOpen318
import all ContactOriginalAffineTestCover318
import all OriginalLineAffineModel318
import all OriginalLineFiniteFlatPID318
import all RelativeOriginalPolynomialAlgebra318
import all RelativeOriginalChartSections318
import all RelativeOriginalAffineChart318
import all ContactOriginalRelativePolynomialCharts318
import all ContactOriginalLineFiniteChart318
import all ContactOriginalLineBothCharts318
import all OriginalLaurentProjectiveOverlap318
import all ContactOriginalLaurentOverlap318
import all ContactOriginalLineOverlap318
import all ContactOverlapTensorCharts318
import all RelativeOriginalAffineChartMap318
import all ContactOriginalRelativeOverlap318
import all RelativeOriginalLaurentAlgebra318
import all RelativeOriginalOverlapRingMap318
import all ContactOriginalRelativeOverlapCoordinates318
import all AdjunctionOriginalUnitTransport318
import all OriginalLineAffineBaseChange318
import all AffineGlobalSectionCoherence318
import all TildePullbackMate318
import all OriginalLineBaseChangeUnit318
import all OriginalAffineLinePathSections318
import all ContactOriginalRelativeLineOverlap318
import all ScalarRestrictionOriginalSpan318
import all RelativeLaurentCoefficientTransport318
import all RelativeLaurentRingSpan318
import all ContactOriginalFiniteRingSpan318
import all AffineSpecOriginalRingTransport318
import all ContactOriginalInfinityRingSpan318
import all RelativeLaurentScalar318
import all RelativeLaurentClearing318
import all RelativeLaurentGeneratorBound318
import all RelativePolynomialChartGenerators318
import all RelativePolynomialChartBound318
import all ContactOriginalRelativeOverlapSpan318
import all RelativeLaurentFiniteQuotient318
import all RelativePolynomialChartFinite318
import all ContactOriginalRelativeFiniteCech318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ContactWholeInfinityAlgebra318,`ContactWholeInfinityScheme318,`OriginalAffineTestOpen318,`ContactOriginalAffineTestCover318,`OriginalLineAffineModel318,`OriginalLineFiniteFlatPID318,`RelativeOriginalPolynomialAlgebra318,`RelativeOriginalChartSections318,`RelativeOriginalAffineChart318,`ContactOriginalRelativePolynomialCharts318,`ContactOriginalLineFiniteChart318,`ContactOriginalLineBothCharts318,`OriginalLaurentProjectiveOverlap318,`ContactOriginalLaurentOverlap318,`ContactOriginalLineOverlap318,`ContactOverlapTensorCharts318,`RelativeOriginalAffineChartMap318,`ContactOriginalRelativeOverlap318,`RelativeOriginalLaurentAlgebra318,`RelativeOriginalOverlapRingMap318,`ContactOriginalRelativeOverlapCoordinates318,`AdjunctionOriginalUnitTransport318,`OriginalLineAffineBaseChange318,`AffineGlobalSectionCoherence318,`TildePullbackMate318,`OriginalLineBaseChangeUnit318,`OriginalAffineLinePathSections318,`ContactOriginalRelativeLineOverlap318,`ScalarRestrictionOriginalSpan318,`RelativeLaurentCoefficientTransport318,`RelativeLaurentRingSpan318,`ContactOriginalFiniteRingSpan318,`AffineSpecOriginalRingTransport318,`ContactOriginalInfinityRingSpan318,`RelativeLaurentScalar318,`RelativeLaurentClearing318,`RelativeLaurentGeneratorBound318,`RelativePolynomialChartGenerators318,`RelativePolynomialChartBound318,`ContactOriginalRelativeOverlapSpan318,`RelativeLaurentFiniteQuotient318,`RelativePolynomialChartFinite318,`ContactOriginalRelativeFiniteCech318]
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
