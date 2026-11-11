module
public import HolomorphicTranslationGauge318
public import PELOriginalDegreeOneRatioHolomorphy318
public section
noncomputable section
namespace PELOriginalMixedTranslationGauge318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationAutomorphy318 PELOriginalDegreeOneRatioBundle318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def domain (a : Index) : Set ComplexVectors :=
  {z | value τ hτ 3 a.1 z≠0 ∧ value τ hτ 2 a.2 z≠0}
@[expose] def gauge (a : Index) (z : ComplexVectors) : ℂ :=
  value τ hτ 3 a.1 z/value τ hτ 2 a.2 z
lemma domain_open (a : Index) : IsOpen (domain τ hτ a) :=
  (isOpen_ne (holomorphic τ hτ 3 a.1).continuous continuous_const).inter
    (isOpen_ne (holomorphic τ hτ 2 a.2).continuous continuous_const)
lemma covers (z : ComplexVectors) : ∃ a,z∈domain τ hτ a := by
  have h3 := PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 z
  have h2 := PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 0 z
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h3
  obtain ⟨j,hj⟩ := Function.ne_iff.mp h2
  exact ⟨(i,j),hi,hj⟩
lemma gauge_nonzero (a : Index) (z : ComplexVectors) (hz : z∈domain τ hτ a) :
    gauge τ hτ a z≠0 := div_ne_zero hz.1 hz.2
lemma gauge_holomorphic (a : Index) (z : ComplexVectors) (hz : z∈domain τ hτ a) :
    DifferentiableAt ℂ (gauge τ hτ a) z :=
  (holomorphic τ hτ 3 a.1 z).div (holomorphic τ hτ 2 a.2 z) hz.2
lemma stable (a : Index) (l : L τ hτ) (z : ComplexVectors) (hz : z∈domain τ hτ a) :
    z+l.val∈domain τ hτ a := by
  constructor
  · rw [original_automorphy]
    exact mul_ne_zero (pow_ne_zero _ (nonzero τ hτ l z)) hz.1
  · rw [original_automorphy]
    exact mul_ne_zero (pow_ne_zero _ (nonzero τ hτ l z)) hz.2
lemma gauge_shift (a : Index) (l : L τ hτ) (z : ComplexVectors) (hz : z∈domain τ hτ a) :
    gauge τ hτ a (z+l.val)=factor τ hτ l z*gauge τ hτ a z := by
  rw [gauge,gauge,original_automorphy,original_automorphy]
  field_simp [nonzero τ hτ l z,hz.2]
  <;> ring

/-- The exact original flat multiplier of translation. Semicharacter
and quadratic terms cancel in the actual two values of the same factor. -/
lemma factor_translation (δ : ComplexVectors) (l : L τ hτ) (z : ComplexVectors) :
    factor τ hτ l (z+δ)/factor τ hτ l z=
      Complex.exp ((Real.pi:ℂ)*PELOriginalHermitianForm318.form τ hτ δ l.val) := by
  rw [factor,factor,←Complex.exp_sub]
  congr 1
  simp only [exponent,PELOriginalHermitianForm318.form_add_left]
  ring

/-- Specialize the generic gluing theorem only after ALL local regular
unit properties have been supplied by the actual sheaf isomorphism.
The original theta gauges and full original automorphy are fixed here. -/
def data (δ : ComplexVectors) (c : (Index × Index) → ComplexVectors → ℂ)
    (hc0 : ∀ a z,z∈domain τ hτ a.1 → z+δ∈domain τ hτ a.2 → c a z≠0)
    (hcd : ∀ a z,z∈domain τ hτ a.1 → z+δ∈domain τ hτ a.2 → DifferentiableAt ℂ (c a) z)
    (hcp : ∀ a (l : L τ hτ) z,z∈domain τ hτ a.1 → z+δ∈domain τ hτ a.2 →
      c a (z+l.val)=c a z)
    (hcc : ∀ a b z,z∈domain τ hτ a.1 → z+δ∈domain τ hτ a.2 →
      z∈domain τ hτ b.1 → z+δ∈domain τ hτ b.2 →
      c a z*(gauge τ hτ b.1 z/gauge τ hτ a.1 z)=
        (gauge τ hτ b.2 (z+δ)/gauge τ hτ a.2 (z+δ))*c b z) :
    HolomorphicTranslationGauge318.Data (L τ hτ).toAddSubgroup δ where
  domain := domain τ hτ
  isOpen_domain := domain_open τ hτ
  cover := covers τ hτ
  gauge := gauge τ hτ
  gauge_ne := gauge_nonzero τ hτ
  gauge_diff := gauge_holomorphic τ hτ
  stable := stable τ hτ
  factor := factor τ hτ
  factor_ne := nonzero τ hτ
  gauge_shift := gauge_shift τ hτ
  coefficient := c
  coefficient_ne := hc0
  coefficient_diff := hcd
  coefficient_periodic := hcp
  compatibility := hcc

/-- This interface consumes the actual gluing data; the substantive
line-isomorphism-to-local-unit construction is separate and mandatory. -/
theorem period_of_data (δ : ComplexVectors)
    (D : HolomorphicTranslationGauge318.Data (L τ hτ).toAddSubgroup δ)
    (hfactor : D.factor=factor τ hτ) : δ∈L τ hτ := by
  apply PELOriginalEntireTranslationCharacter318.original_period τ hτ δ
    (HolomorphicTranslationGauge318.entireValue _ δ D)
    (HolomorphicTranslationGauge318.differentiable _ δ D)
    (HolomorphicTranslationGauge318.nonzero _ δ D 0)
  intro l z
  rw [HolomorphicTranslationGauge318.shift,hfactor,factor_translation]
end PELOriginalMixedTranslationGauge318
