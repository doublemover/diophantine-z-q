module
public import PulledCoordinateMaps318
public import ProjectiveLineCoordinateGenerators318
public import ContactProjectiveLinePullback318
public section
noncomputable section
namespace ContactPulledCoordinates318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
@[expose] def zeroMap := PulledCoordinateMaps318.map
  (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.zeroMap
@[expose] def oneMap := PulledCoordinateMaps318.map
  (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.oneMap
@[expose] def q0 := PulledCoordinateMaps318.sectionTop
  (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.zeroMap
@[expose] def q1 := PulledCoordinateMaps318.sectionTop
  (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.oneMap

/-- The literal pulled first coordinate generates on each complete finite contact chart. -/
theorem zero_branch_isIso (i : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (zeroMap c)) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor (JLineAtlas318.chart ℚ 1)).map
      ProjectiveLineCoordinates318.zeroMap) := ProjectiveLineCoordinateGenerators318.zero_finite_isIso
  exact PulledCoordinateMaps318.restrict_isIso
    (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.zeroMap
    (JLineAtlas318.chart ℚ 1) (ContactIntrinsicFrames318.branchEmbedding c i)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.branch_comparison c i)

/-- The literal pulled second coordinate generates on the whole infinity chart. -/
theorem one_infinity_isIso :
    IsIso ((Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (oneMap c)) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor (JLineAtlas318.chart ℚ 0)).map
      ProjectiveLineCoordinates318.oneMap) := ProjectiveLineCoordinateGenerators318.one_infinity_isIso
  exact PulledCoordinateMaps318.restrict_isIso
    (ContactBicanonicalProjectiveMap318.projectiveMap c) ProjectiveLineCoordinates318.oneMap
    (JLineAtlas318.chart ℚ 0) (InfinityGlobalScheme318.chartEmbedding c)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.infinityRatio c)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.infinity_comparison c)
end ContactPulledCoordinates318
