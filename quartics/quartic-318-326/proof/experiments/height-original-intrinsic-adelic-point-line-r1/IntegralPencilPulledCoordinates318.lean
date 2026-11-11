module
public import IntegralProjectiveCoordinateGenerators318
public import IntegralProjectiveCoordinateRelations318
public import PulledCoordinateMaps318
public section
noncomputable section
namespace IntegralPencilPulledCoordinates318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralGluedModel318 IntegralGluedDifferentialFrames318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

/-- The actual pullback module of the INDEPENDENTLY constructed target O(1). -/
@[expose] def line : (scheme R c).Modules :=
  (Scheme.Modules.pullback (IntegralSectionProjectiveMap318.projectiveMap R c hN)).obj
    (IntegralProjectiveLineOOne318.line R)
@[expose] def zeroMap := PulledCoordinateMaps318.map
  (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.zeroMap R)
@[expose] def oneMap := PulledCoordinateMaps318.map
  (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.oneMap R)
@[expose] def q0 := PulledCoordinateMaps318.sectionTop
  (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.zeroMap R)
@[expose] def q1 := PulledCoordinateMaps318.sectionTop
  (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.oneMap R)

theorem zero_branch_isIso (i : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (branchEmbedding R c i)).map (zeroMap R c hN)) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor (JLineAtlas318.chart R 1)).map
      (IntegralProjectiveLineCoordinates318.zeroMap R)) :=
    IntegralProjectiveCoordinateGenerators318.zero_finite_isIso R
  exact PulledCoordinateMaps318.restrict_isIso
    (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.zeroMap R)
    (JLineAtlas318.chart R 1) (branchEmbedding R c i)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
      (IntegralBranchCoordinates318.sourceT R c i)).toRingHom))
    (IntegralSectionProjectiveMap318.projectiveMap_local R c hN (some i))

theorem one_infinity_isIso :
    IsIso ((Scheme.Modules.restrictFunctor (infinityChart R c)).map (oneMap R c hN)) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor (JLineAtlas318.chart R 0)).map
      (IntegralProjectiveLineCoordinates318.oneMap R)) :=
    IntegralProjectiveCoordinateGenerators318.one_infinity_isIso R
  exact PulledCoordinateMaps318.restrict_isIso
    (IntegralSectionProjectiveMap318.projectiveMap R c hN) (IntegralProjectiveLineCoordinates318.oneMap R)
    (JLineAtlas318.chart R 0) (infinityChart R c)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
      (IntegralOriginalContactPencil318.infinityRatioValue R c)).toRingHom))
    (IntegralSectionProjectiveMap318.projectiveMap_local R c hN none)
end IntegralPencilPulledCoordinates318
