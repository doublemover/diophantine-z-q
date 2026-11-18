module
public import PELOriginalHyperplaneSectionCoordinates318
public import PELOriginalCandidateHyperplaneComparison318
public section
noncomputable section
namespace PELOriginalAlgebraicHyperplaneAnalyticComparison318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalAlgebraicHyperplaneImage318 PELOriginalCandidateHomeomorph318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open DiscreteComplexPeriodAtlas318 ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Evaluate the ACTUAL regular transition coefficient by the genuine
Spec(C) point and its map on global sections. -/
@[expose] def coefficientValue (k i : Label 3)
    (f : CoordinateChart τ hτ k →ₐ[ℂ] ℂ) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop (ratios τ hτ k i))

lemma coefficientValue_eq (k i : Label 3)
    (f : CoordinateChart τ hτ k →ₐ[ℂ] ℂ) :
    coefficientValue τ hτ k i f = f (ratioElement τ hτ k i) := by
  have he := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toRingHom)) (ratioElement τ hτ k i)
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ k))).inv
        (ratioElement τ hτ k i))) = _
  rw [←he]
  exact Iso.inv_hom_id_apply _ _

/-- The actual algebraic frame transition evaluates to the independently
constructed dual-tautological O(1) transition, with its correct sign.
The whole-sheaf transition was proved before taking this evaluation. -/
theorem original_transition (k i : Label 3) (z : ComplexVectors)
    (hk : value τ hτ 3 k z ≠ 0) :
    coefficientValue τ hτ k i (algebraEvaluation τ hτ z k hk) =
      ComplexProjectiveHyperplaneBundle318.transition (Label 3) i k
        (comparison τ hτ (projection (P τ) z)).val := by
  rw [coefficientValue_eq,actual_ratio_evaluation,comparison_cover]
  rfl

/-- Every point of the FULL independent candidate and every valid chart
is covered by the exact algebraic-to-analytic transition comparison.
No old primitive denominator or selected-open condition survives. -/
theorem every_candidate_transition (p : CandidatePoints τ hτ) (k i : Label 3)
    (hk : p.val ∈ domain (Label 3) k) :
    ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 k z ≠ 0,
      comparison τ hτ (projection (P τ) z) = p ∧
      coefficientValue τ hτ k i (algebraEvaluation τ hτ z k hz) =
        ComplexProjectiveHyperplaneBundle318.transition (Label 3) i k p.val := by
  obtain ⟨z,hz⟩ := quotient_surjective (P τ) ((comparison τ hτ).symm p)
  have hp : comparison τ hτ (projection (P τ) z) = p := by
    rw [hz]
    exact (comparison τ hτ).apply_symm_apply p
  have hd : coveringMap τ hτ 1 z ∈ domain (Label 3) k := by
    rw [←comparison_cover,hp]
    exact hk
  have htheta : value τ hτ 3 k z ≠ 0 :=
    (mk_mem_domain (Label 3) k (coverVector τ hτ 1 z) (coverVector_nonzero τ hτ 1 z)).mp hd
  refine ⟨z,htheta,hp,?_⟩
  rw [original_transition,hp]

/-- These are transitions of the SAME algebraic image sheaf in any
anchor normalization: its actual global cubic sections and all nine
frames have exactly the regular coefficients evaluated above. -/
theorem algebraic_frame_certificate (anchor k i : Label 3) :
    (Scheme.Modules.restrictFunctor (PELOriginalCandidateNineChartCover318.chartMap τ hτ k)).map
      (PELOriginalHyperplaneSectionCoordinates318.section τ hτ anchor i) =
    (Scheme.Modules.restrictUnitIso (PELOriginalCandidateNineChartCover318.chartMap τ hτ k)).hom ≫
      GlobalScalarSheafEndomorphism318.endomorphism _ (ratios τ hτ k i) ≫
        (PELOriginalHyperplaneChartFrames318.frame τ hτ anchor k).hom :=
  PELOriginalHyperplaneSectionCoordinates318.section_in_frame τ hτ anchor k i

/-- The original cubic power bundle compares with the complex line
bundle having precisely the evaluated algebraic hyperplane atlas above.
This uses the existing whole-base homeomorphism and local holomorphy,
not a claim that an abstract analytification functor has been built. -/
@[expose] def originalComparison :=
  PELOriginalCandidateHyperplaneComparison318.comparisonTotal τ hτ

lemma originalComparison_base (p : PELOriginalPolarizationPowerBundle318.PowerTotal τ hτ 3) :
    (originalComparison τ hτ p).1 = comparison τ hτ p.1 :=
  PELOriginalCandidateHyperplaneComparison318.comparison_base τ hτ p

/-- Fiberwise C-linearity of the same original cubic comparison. -/
@[expose] def originalFiberComparison (q : Base τ) :=
  PELOriginalCandidateHyperplaneComparison318.fiberComparison τ hτ q

/-- Both local comparison maps are holomorphic on every genuine overlap
of an original torus chart and the algebraic hyperplane chart atlas. -/
theorem original_local_biholomorphy (a : ComplexVectors) (k : Label 3)
    (p : PELOriginalPolarizationPowerBundle318.PowerTotal τ hτ 3)
    (ha : p.1 ∈ PELOriginalPolarizationTransitions318.baseSet τ hτ a)
    (hk : (comparison τ hτ p.1).val ∈ domain (Label 3) k) :
    DifferentiableAt ℂ (PELOriginalHyperplanePullbackHolomorphy318.forwardLocal τ hτ 1 k)
      (PELOriginalHyperplanePullbackHolomorphy318.originalCoordinates τ hτ 1 a p) ∧
    DifferentiableAt ℂ (PELOriginalHyperplanePullbackHolomorphy318.inverseLocal τ hτ 1 k)
      (PELOriginalHyperplanePullbackHolomorphy318.pullbackCoordinates τ hτ 1 a k
        (PELOriginalHyperplanePullbackTopology318.homeomorph τ hτ 1 p)) :=
  PELOriginalCandidateHyperplaneComparison318.local_biholomorphy τ hτ a k p ha hk
end PELOriginalAlgebraicHyperplaneAnalyticComparison318
