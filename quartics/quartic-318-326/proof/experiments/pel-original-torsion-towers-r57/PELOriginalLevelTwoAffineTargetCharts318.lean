module
public import PELOriginalLevelTwoNormalizedColumns318
public import AffineProjectiveScaledVector318
public section
noncomputable section
namespace PELOriginalLevelTwoAffineTargetCharts318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalLevelTwoCubicProducts318
open PELOriginalLevelTwoNormalizedColumns318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (s : Label 2)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFinite : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) := chart_finite_type τ hτ j
local instance normalizedReduced : _root_.IsReduced (Chart τ hτ j s) := by infer_instance
local instance normalizedFinite : Algebra.FiniteType ℂ (Chart τ hτ j s) := by infer_instance
local instance standardGrading : GradedAlgebra
    (ComplexProjectiveMarkerPoint318.grading (ι := Label 2)) := MvPolynomial.gradedAlgebra

lemma normalized_span : Ideal.span (Set.range (normalized τ hτ j s))=⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self s))
  rw [normalized_self]
  exact isUnit_one

/-- Actual regular coordinates with s-coordinate ONE give precisely the
same scheme morphism as the global level-two map on D(B_s). -/
theorem normalized_morphism :
    RankOneAffineColumnCover318.entryMap (coordinate τ hτ j) (s,s) ≫
      PELOriginalLevelTwoChartMorphism318.morphism τ hτ j =
    AffineComplexProjectiveVector318.morphism (normalized τ hτ j s)
      (normalized_span τ hτ j s) := by
  rw [local_scheme_map]
  exact (AffineProjectiveScaledVector318.morphism_eq
    (RankOneAffineColumnCover318.column (coordinate τ hτ j) (s,s))
    (normalized τ hτ j s) (RankOneAffineColumnCover318.column_span _ _)
    (normalized_span τ hτ j s) (IsLocalization.Away.invSelf (denominator τ hτ j s))
    (fun _ => rfl)).symm

/-- ALL scheme points of D(B_s) map into the actual s-th projective
standard open, not only its complex points. This is the full open-chart
input for the algebraic hyperplane pullback. -/
theorem target_chart_preimage :
    (RankOneAffineColumnCover318.entryMap (coordinate τ hτ j) (s,s) ≫
      PELOriginalLevelTwoChartMorphism318.morphism τ hτ j) ⁻¹ᵁ
      Proj.basicOpen (ComplexProjectiveMarkerPoint318.grading (ι := Label 2))
        (MvPolynomial.X s) = ⊤ := by
  rw [normalized_morphism]
  rw [AffineComplexProjectiveVector318.morphism,
    ComplexProjectiveRegularVector318.homogeneous_preimage _ _ _ _ 1 (by norm_num)
      (MvPolynomial.isHomogeneous_X ℂ s)]
  change (Spec (CommRingCat.of (Chart τ hτ j s))).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (Chart τ hτ j s))).inv (normalized τ hτ j s s)) = ⊤
  rw [normalized_self,map_one]
  exact Scheme.basicOpen_of_isUnit _ isUnit_one
end PELOriginalLevelTwoAffineTargetCharts318
