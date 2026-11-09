module
public import IntegralPencilPulledCoordinates318
public import PullbackLocalRelations318
public section
noncomputable section
namespace IntegralPencilPulledRatios318
open AlgebraicGeometry CategoryTheory Polynomial
open IntegralGluedModel318 IntegralGluedDifferentialFrames318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact affine-coordinate evaluation over the original arbitrary base. -/
theorem coordinate (a : S) :
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) a).toRingHom)).appTop
      (IntegralProjectiveLineCoordinates318.coordinate R)=(Scheme.ΓSpecIso (CommRingCat.of S)).inv a := by
  have h := congrArg (fun f => f X) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.aeval (R:=R) a).toRingHom))
  have hh := h.symm
  change (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) a).toRingHom)).appTop
    (IntegralProjectiveLineCoordinates318.coordinate R)=
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ((Polynomial.aeval (R:=R) a) X) at hh
  rw [Polynomial.aeval_X] at hh
  exact hh

variable (R) (c : Fin 4 → Rˣ)
variable (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R))

theorem branch_relation (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (branchEmbedding R c i)).map
      (IntegralPencilPulledCoordinates318.oneMap R c hN)=
    (Scheme.Modules.restrictFunctor (branchEmbedding R c i)).map
      (IntegralPencilPulledCoordinates318.zeroMap R c hN) ≫
      ModuleScalar318.map ((IntegralPencilPulledCoordinates318.line R c hN).restrict
        (branchEmbedding R c i))
        ((Scheme.ΓSpecIso (CommRingCat.of (IntegralBranchCoordinates318.B R c i))).inv
          (IntegralBranchCoordinates318.sourceT R c i)) := by
  have hr : LocalCoordinateRelation318.localMap (JLineAtlas318.chart R 1)
      (IntegralProjectiveLineCoordinates318.oneMap R)=
      ClutchedModule318.multiply (IntegralProjectiveLineCoordinates318.coordinate R) ≫
        LocalCoordinateRelation318.localMap (JLineAtlas318.chart R 1)
          (IntegralProjectiveLineCoordinates318.zeroMap R) :=
    IntegralProjectiveCoordinateRelations318.finite_relation R
  have h := PullbackLocalRelations318.relation
    (IntegralSectionProjectiveMap318.projectiveMap R c hN) (JLineAtlas318.chart R 1)
    (branchEmbedding R c i)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) (IntegralBranchCoordinates318.sourceT R c i)).toRingHom))
    (IntegralSectionProjectiveMap318.projectiveMap_local R c hN (some i))
    (IntegralProjectiveLineCoordinates318.zeroMap R) (IntegralProjectiveLineCoordinates318.oneMap R)
    (IntegralProjectiveLineCoordinates318.coordinate R) hr
  rw [coordinate] at h
  exact h

theorem infinity_relation :
    (Scheme.Modules.restrictFunctor (infinityChart R c)).map
      (IntegralPencilPulledCoordinates318.zeroMap R c hN)=
    (Scheme.Modules.restrictFunctor (infinityChart R c)).map
      (IntegralPencilPulledCoordinates318.oneMap R c hN) ≫
      ModuleScalar318.map ((IntegralPencilPulledCoordinates318.line R c hN).restrict (infinityChart R c))
        ((Scheme.ΓSpecIso (CommRingCat.of (IntegralInfinityChart318.Order R c))).inv
          (IntegralOriginalContactPencil318.infinityRatioValue R c)) := by
  have hr : LocalCoordinateRelation318.localMap (JLineAtlas318.chart R 0)
      (IntegralProjectiveLineCoordinates318.zeroMap R)=
      ClutchedModule318.multiply (IntegralProjectiveLineCoordinates318.coordinate R) ≫
        LocalCoordinateRelation318.localMap (JLineAtlas318.chart R 0)
          (IntegralProjectiveLineCoordinates318.oneMap R) :=
    IntegralProjectiveCoordinateRelations318.infinity_relation R
  have h := PullbackLocalRelations318.relation
    (IntegralSectionProjectiveMap318.projectiveMap R c hN) (JLineAtlas318.chart R 0) (infinityChart R c)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R)
      (IntegralOriginalContactPencil318.infinityRatioValue R c)).toRingHom))
    (IntegralSectionProjectiveMap318.projectiveMap_local R c hN none)
    (IntegralProjectiveLineCoordinates318.oneMap R) (IntegralProjectiveLineCoordinates318.zeroMap R)
    (IntegralProjectiveLineCoordinates318.coordinate R) hr
  rw [coordinate] at h
  exact h
end IntegralPencilPulledRatios318
