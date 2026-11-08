module
public import PullbackLocalRelations318
public import ProjectiveLineCoordinateRelations318
public import PolynomialCoordinatePullback318
public import ContactPulledCoordinates318
public section
noncomputable section
namespace ContactPulledRatios318
open AlgebraicGeometry CategoryTheory Polynomial
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)
/-- The actual pulled first/second coordinates have the exact finite ratio,
on the entire chart and as a sheaf-morphism identity. -/
theorem branch_relation (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (ContactPulledCoordinates318.oneMap c)=
    (Scheme.Modules.restrictFunctor (ContactIntrinsicFrames318.branchEmbedding c i)).map
      (ContactPulledCoordinates318.zeroMap c) ≫
      ModuleScalar318.map ((ContactProjectiveLinePullback318.line c).restrict
        (ContactIntrinsicFrames318.branchEmbedding c i))
        ((Scheme.ΓSpecIso (CommRingCat.of (ContactIntrinsicFrames318.BranchRing c i))).inv
          (ContactBicanonicalRatios318.branchRatio c i)) := by
  have hr : LocalCoordinateRelation318.localMap (JLineAtlas318.chart ℚ 1)
      ProjectiveLineCoordinates318.oneMap=
      ClutchedModule318.multiply ProjectiveLineCoordinates318.coordinate ≫
        LocalCoordinateRelation318.localMap (JLineAtlas318.chart ℚ 1)
          ProjectiveLineCoordinates318.zeroMap := ProjectiveLineCoordinateRelations318.finite_relation
  have h := PullbackLocalRelations318.relation
    (ContactBicanonicalProjectiveMap318.projectiveMap c) (JLineAtlas318.chart ℚ 1)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.branchRatio c i)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.branch_comparison c i)
    ProjectiveLineCoordinates318.zeroMap ProjectiveLineCoordinates318.oneMap
    ProjectiveLineCoordinates318.coordinate hr
  rw [PolynomialCoordinatePullback318.coordinate] at h
  exact h

/-- The reciprocal coordinate ratio is regular on the entire infinity chart,
including its center, and is normalized by the same target coordinate. -/
theorem infinity_relation :
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactPulledCoordinates318.zeroMap c)=
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactPulledCoordinates318.oneMap c) ≫
      ModuleScalar318.map ((ContactProjectiveLinePullback318.line c).restrict
        (InfinityGlobalScheme318.chartEmbedding c))
        ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv
          (ContactBicanonicalRatios318.infinityRatio c)) := by
  have hr : LocalCoordinateRelation318.localMap (JLineAtlas318.chart ℚ 0)
      ProjectiveLineCoordinates318.zeroMap=
      ClutchedModule318.multiply ProjectiveLineCoordinates318.coordinate ≫
        LocalCoordinateRelation318.localMap (JLineAtlas318.chart ℚ 0)
          ProjectiveLineCoordinates318.oneMap := ProjectiveLineCoordinateRelations318.infinity_relation
  have h := PullbackLocalRelations318.relation
    (ContactBicanonicalProjectiveMap318.projectiveMap c) (JLineAtlas318.chart ℚ 0)
    (InfinityGlobalScheme318.chartEmbedding c)
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (ContactBicanonicalRatios318.infinityRatio c)).toRingHom))
    (by rw [ContactBicanonicalProjectiveMap318.projectiveMap_eq]
        exact ContactBicanonicalProjectiveMap318.infinity_comparison c)
    ProjectiveLineCoordinates318.oneMap ProjectiveLineCoordinates318.zeroMap
    ProjectiveLineCoordinates318.coordinate hr
  exact h.trans (congrArg (fun a : Γ(ReciprocalInfinityNormalization318.neighborhood c,⊤) =>
    (Scheme.Modules.restrictFunctor (InfinityGlobalScheme318.chartEmbedding c)).map
      (ContactPulledCoordinates318.oneMap c) ≫
      ModuleScalar318.map ((ContactProjectiveLinePullback318.line c).restrict
        (InfinityGlobalScheme318.chartEmbedding c)) a)
    (PolynomialCoordinatePullback318.coordinate (ContactBicanonicalRatios318.infinityRatio c)))
end ContactPulledRatios318
