module
import all FaithfullyFlatFinitePresentation318
import all OriginalLineAffineModel318
import all FaithfullyFlatLineModule318
import all AffineRankOneLine318
import all AffineCoalgebraModule318
import all AffineCoalgebraLine318
import all TensorPushoutModule318
import all AffineModuleBaseChange318
import all AffineModuleMate318
import all AffineOverlapCoaction318
import all AffineOverlapDiagonal318
import all ScalarExtensionCongr318
import all ScalarExtensionComposition318
import all AffineCechRings318
import all AffineTripleCoactionCoordinates318
import all AffineTripleOverlapMaps318
import all AffineTripleCoordinateLaws318
import all AffineOverlapCoassociativity318
import all AffineCocycleLine318
import all AffineGlobalSectionCoherence318
import all TildePullbackMate318
import all AffineComparisonMates318
import all TildePullbackComposition318
import all TildePullbackIdentity318
import all OriginalLineAffineBaseChange318
import all OriginalLineOverlapCoaction318
import all TildePullbackInverseComposition318
import all OriginalLineComparisonComposition318
import all OriginalLineComparisonIdentity318
import all OriginalLineNamedComparison318
import all AffineSectionConjugation318
import all OriginalGeometricEdge318
import all OriginalGeometricTriple318
import all OriginalGeometricDiagonal318
import all AffineSplitDiagonalTranspose318
import all OriginalGeometricAffineLine318
import all OverlapMorphismCoaction318
import all GeometricAffineDescentData318
import all FaithfullyFlatTildeFaithful318
import all GeometricAffineDescendedMorphism318
import all GeometricAffineDescendedFunctor318
import all ActualOverlapDiagram318
import all ActualAffineDoubleNerve318
import all ActualAffineTripleMaps318
import all ActualAffineTripleNerve318
import all SheafPathTransport318
import all ActualAffineSheafData318
import all ActualAffineTensorTransport318
import all ActualAffineTensorLaws318
import all ActualAffineLineReconstruction318
import all CanonicalScalarOverlap318
import all CanonicalTildeOverlap318
import all CanonicalGeometricOverlap318
import all ReconstructedOverlapCompatibility318
import all SheafIsoTransport318
import all CanonicalSheafOverlap318
import all ActualCanonicalOverlap318
import all ActualAffineEffectiveComparison318
import all SheafTransportIntertwiner318
import all ActualAffineDescentData318
import all ActualAffineDescendedMaps318
import all CanonicalActualDescentLaws318
import all CanonicalActualDescentFunctor318
import all OriginalAffineLineFaithfulness318
import all CanonicalScalarMorphismDescent318
import all CanonicalTildeMorphismTransport318
import all ActualTildeMorphismDescent318
import all OriginalAffineMorphismDescent318
import all OriginalAffineReconstructionUnit318
import all ActualDescentBaseChangeDiagram318
import all SheafArrowBaseChange318
import all OriginalSchemeDescentData318
import all OriginalSchemeDescentBaseChange318
import all OriginalSchemeDescentBaseChangeMaps318
import all AffineChangedBaseEffectivity318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FaithfullyFlatFinitePresentation318,`OriginalLineAffineModel318,`FaithfullyFlatLineModule318,`AffineRankOneLine318,`AffineCoalgebraModule318,`AffineCoalgebraLine318,`TensorPushoutModule318,`AffineModuleBaseChange318,`AffineModuleMate318,`AffineOverlapCoaction318,`AffineOverlapDiagonal318,`ScalarExtensionCongr318,`ScalarExtensionComposition318,`AffineCechRings318,`AffineTripleCoactionCoordinates318,`AffineTripleOverlapMaps318,`AffineTripleCoordinateLaws318,`AffineOverlapCoassociativity318,`AffineCocycleLine318,`AffineGlobalSectionCoherence318,`TildePullbackMate318,`AffineComparisonMates318,`TildePullbackComposition318,`TildePullbackIdentity318,`OriginalLineAffineBaseChange318,`OriginalLineOverlapCoaction318,`TildePullbackInverseComposition318,`OriginalLineComparisonComposition318,`OriginalLineComparisonIdentity318,`OriginalLineNamedComparison318,`AffineSectionConjugation318,`OriginalGeometricEdge318,`OriginalGeometricTriple318,`OriginalGeometricDiagonal318,`AffineSplitDiagonalTranspose318,`OriginalGeometricAffineLine318,`OverlapMorphismCoaction318,`GeometricAffineDescentData318,`FaithfullyFlatTildeFaithful318,`GeometricAffineDescendedMorphism318,`GeometricAffineDescendedFunctor318,`ActualOverlapDiagram318,`ActualAffineDoubleNerve318,`ActualAffineTripleMaps318,`ActualAffineTripleNerve318,`SheafPathTransport318,`ActualAffineSheafData318,`ActualAffineTensorTransport318,`ActualAffineTensorLaws318,`ActualAffineLineReconstruction318,`CanonicalScalarOverlap318,`CanonicalTildeOverlap318,`CanonicalGeometricOverlap318,`ReconstructedOverlapCompatibility318,`SheafIsoTransport318,`CanonicalSheafOverlap318,`ActualCanonicalOverlap318,`ActualAffineEffectiveComparison318,`SheafTransportIntertwiner318,`ActualAffineDescentData318,`ActualAffineDescendedMaps318,`CanonicalActualDescentLaws318,`CanonicalActualDescentFunctor318,`OriginalAffineLineFaithfulness318,`CanonicalScalarMorphismDescent318,`CanonicalTildeMorphismTransport318,`ActualTildeMorphismDescent318,`OriginalAffineMorphismDescent318,`OriginalAffineReconstructionUnit318,`ActualDescentBaseChangeDiagram318,`SheafArrowBaseChange318,`OriginalSchemeDescentData318,`OriginalSchemeDescentBaseChange318,`OriginalSchemeDescentBaseChangeMaps318,`AffineChangedBaseEffectivity318]
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
