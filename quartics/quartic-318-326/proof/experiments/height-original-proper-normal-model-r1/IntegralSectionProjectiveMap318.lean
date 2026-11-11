module
public import IntegralOriginalContactPencil318
public section
noncomputable section
namespace IntegralSectionProjectiveMap318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralGluedModel318 IntegralGluedDifferentialFrames318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- Actual affine evaluation at the uniquely characterized finite ratio of
the original section pair. The coordinate convention is [q1:q0]. -/
@[expose] def branchMap (i : Fin 4) : chart R c (some i) ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
    (IntegralBranchCoordinates318.sourceT R c i)).toRingHom) ≫ JLineAtlas318.chart R 1
@[expose] def infinityMap : chart R c none ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
    (IntegralOriginalContactPencil318.infinityRatioValue R c)).toRingHom) ≫ JLineAtlas318.chart R 0

theorem branch_polynomial (i : Fin 4) :
    (Polynomial.aeval (R:=R) (IntegralBranchCoordinates318.sourceT R c i)).toRingHom=
      (algebraMap (IntegralSourceBranches318.SourceOrder R c) (IntegralBranchCoordinates318.B R c i)).comp
        (algebraMap R[X] (IntegralSourceBranches318.SourceOrder R c)) := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [Polynomial.aeval_C,RingHom.comp_apply]
    exact IsScalarTower.algebraMap_apply R (IntegralSourceBranches318.SourceOrder R c)
      (IntegralBranchCoordinates318.B R c i) r
  · rw [Polynomial.aeval_X]
    rfl

theorem branch_comparison (i : Fin 4) :
    branchEmbedding R c i ≫ IntegralOriginalContactPencil318.projection R c=branchMap R c i := by
  unfold branchEmbedding branchMap
  rw [Category.assoc,IntegralOriginalContactPencil318.finite_restriction,
    branch_polynomial,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))
@[expose] def localMap : (i : Option (Fin 4)) →
    (IntegralOriginalGlobalSmooth318.smoothCover R c hN).X i ⟶ ProjectiveJLine318.scheme R
  | none => infinityMap R c
  | some i => branchMap R c i

theorem local_comparison (i : Option (Fin 4)) :
    (IntegralOriginalGlobalSmooth318.smoothCover R c hN).f i ≫
      IntegralOriginalContactPencil318.projection R c=localMap R c hN i := by
  cases i with
  | none => exact IntegralOriginalContactPencil318.infinity_restriction R c
  | some i => exact branch_comparison R c i

theorem local_compatible (i j : Option (Fin 4)) :
    pullback.fst ((IntegralOriginalGlobalSmooth318.smoothCover R c hN).f i)
      ((IntegralOriginalGlobalSmooth318.smoothCover R c hN).f j) ≫ localMap R c hN i=
      pullback.snd _ _ ≫ localMap R c hN j := by
  rw [←local_comparison,←local_comparison,←Category.assoc,←Category.assoc,pullback.condition]

/-- The scheme morphism obtained from the actual global pair's unique
ratios on all five original charts, not just a rational function. -/
@[expose] def projectiveMap : scheme R c ⟶ ProjectiveJLine318.scheme R :=
  (IntegralOriginalGlobalSmooth318.smoothCover R c hN).glueMorphisms
    (localMap R c hN) (local_compatible R c hN)

theorem projectiveMap_local (i : Option (Fin 4)) :
    (IntegralOriginalGlobalSmooth318.smoothCover R c hN).f i ≫ projectiveMap R c hN=
      localMap R c hN i :=
  (IntegralOriginalGlobalSmooth318.smoothCover R c hN).ι_glueMorphisms _ _ i

/-- Exact equality of scheme morphisms: the original J² pair defines the
original t contact pencil, rather than the auxiliary y0 projection. -/
theorem projectiveMap_eq : projectiveMap R c hN=IntegralOriginalContactPencil318.projection R c := by
  apply (IntegralOriginalGlobalSmooth318.smoothCover R c hN).hom_ext
  intro i
  exact (projectiveMap_local R c hN i).trans (local_comparison R c hN i).symm
end IntegralSectionProjectiveMap318
