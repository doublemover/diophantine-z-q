module
public import PELOriginalTranslationFrameValues318
public import PELOriginalTranslationLineClass318
public section
noncomputable section
namespace PELOriginalTranslationLineStabilizer318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalPolarizationTransitions318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318
variable (τ : ℂ) (hτ : 0 < τ.im) (δ : ComplexVectors)
variable (E : sheaf τ hτ ≅ (Scheme.Modules.pullback (translate τ hτ δ)).obj (sheaf τ hτ))

/-- ALL hypotheses of analytic gluing are now produced from the genuine
whole algebraic line isomorphism. No analytic scalar, character,
continuous bundle map or divisor-invariance premise is supplied. -/
@[expose] def data : HolomorphicTranslationGauge318.Data
    (PELOriginalPolarizationAutomorphy318.L τ hτ).toAddSubgroup δ where
  domain := chartDomain τ hτ
  isOpen_domain a := isOpen_domain τ hτ (opens τ hτ a)
  cover := chart_cover τ hτ
  gauge := chartGauge τ hτ
  gauge_ne a z hz := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z
    (theta_nonzero τ hτ a z hz)
  gauge_diff a z hz := PELOriginalMixedTranslationGauge318.gauge_holomorphic τ hτ a.val z
    (theta_nonzero τ hτ a z hz)
  stable a l z hz := (domain_period τ hτ (opens τ hτ a) l z).mpr hz
  factor := PELOriginalPolarizationAutomorphy318.factor τ hτ
  factor_ne := PELOriginalPolarizationAutomorphy318.nonzero τ hτ
  gauge_shift a l z hz := PELOriginalMixedTranslationGauge318.gauge_shift τ hτ a.val l z
    (theta_nonzero τ hτ a z hz)
  coefficient := coefficient τ hτ δ E
  coefficient_ne := coefficient_nonzero τ hτ δ E
  coefficient_diff := coefficient_holomorphic τ hτ δ E
  coefficient_periodic a l z _ _ := coefficient_periodic τ hτ δ E a l z
  compatibility := coefficient_compatibility τ hτ δ E

/-- A literal nowhere-zero entire scalar on ORIGINAL C², actually
constructed from the line isomorphism and its whole regular frame units. -/
@[expose] def entireScalar : ComplexVectors → ℂ :=
  HolomorphicTranslationGauge318.entireValue _ δ (data τ hτ δ E)
lemma entireScalar_differentiable : Differentiable ℂ (entireScalar τ hτ δ E) :=
  HolomorphicTranslationGauge318.differentiable _ δ (data τ hτ δ E)
lemma entireScalar_nonzero (z : ComplexVectors) : entireScalar τ hτ δ E z≠0 :=
  HolomorphicTranslationGauge318.nonzero _ δ (data τ hτ δ E) z
lemma entireScalar_shift (l : PELOriginalPolarizationAutomorphy318.L τ hτ) (z : ComplexVectors) :
    entireScalar τ hτ δ E (z+l.val)=
      Complex.exp ((Real.pi:ℂ)*PELOriginalHermitianForm318.form τ hτ δ l.val)*
        entireScalar τ hτ δ E z := by
  rw [entireScalar,HolomorphicTranslationGauge318.shift]
  change (PELOriginalPolarizationAutomorphy318.factor τ hτ l (z+δ)/
    PELOriginalPolarizationAutomorphy318.factor τ hτ l z)*_=_
  rw [PELOriginalMixedTranslationGauge318.factor_translation]

/-- The same algebraic isomorphism produces the exact exponential
character for the original Hermitian polarization and FULL lattice. -/
theorem exponential_character : ∃ ℓ : ComplexVectors →ₗ[ℂ] ℂ,
    ∀ l : PELOriginalPolarizationAutomorphy318.L τ hτ,
      Complex.exp (ℓ l.val)=
        Complex.exp ((Real.pi:ℂ)*PELOriginalHermitianForm318.form τ hτ δ l.val) :=
  PELOriginalEntireTranslationCharacter318.exponential_character τ hτ δ
    (entireScalar τ hτ δ E) (entireScalar_differentiable τ hτ δ E)
    (entireScalar_nonzero τ hτ δ E 0) (entireScalar_shift τ hτ δ E)

/-- Trivial translation stabilizer of the ACTUAL algebraic degree-one
line. This is not yet an isomorphism to a represented dual variety. -/
theorem period : δ∈PELOriginalPolarizationAutomorphy318.L τ hτ :=
  PELOriginalMixedTranslationGauge318.period_of_data τ hτ δ (data τ hτ δ E) rfl

/-- Every original complex point whose genuine translated line is
isomorphic to the original line is the identity point. -/
theorem point_zero (q : Base τ)
    (E : sheaf τ hτ ≅ (Scheme.Modules.pullback
      (PELOriginalTranslationAutomorphisms318.translation τ hτ q)).obj (sheaf τ hτ)) : q=0 := by
  obtain ⟨δ,rfl⟩ := quotient_surjective (P τ) q
  have hδ := period τ hτ δ E
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change δ∈PELOriginalPeriodLattice318.lattice τ hτ at hδ
  rw [PELOriginalPeriodLattice318.exact_period_subgroup τ hτ]
  exact hδ
end PELOriginalTranslationLineStabilizer318
