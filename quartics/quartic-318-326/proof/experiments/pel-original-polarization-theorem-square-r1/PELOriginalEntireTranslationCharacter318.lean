module
public import CompactPeriodNormBound318
public import PELOriginalExponentialLatticeCharacter318
public import Mathlib.Analysis.Complex.Liouville
public section
noncomputable section
namespace PELOriginalEntireTranslationCharacter318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalHermitianForm318 PELOriginalPeriodLattice318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance periodsDiscrete : DiscreteTopology (periodSubgroup representation order τ) := original_discrete τ hτ
local instance originalCompact : CompactSpace (PeriodQuotient representation order τ) := original_compact τ hτ

/-- Correct by the COMPLEX-LINEAR first-slot Hermitian functional.
The lattice multiplier need not become one; its NORM becomes one. -/
@[expose] def corrected (δ : ComplexVectors) (f : ComplexVectors → ℂ) (z : ComplexVectors) : ℂ :=
  f z*Complex.exp (-((Real.pi:ℂ)*form τ hτ z δ))

theorem correction_entire (δ : ComplexVectors) (f : ComplexVectors → ℂ)
    (hf : Differentiable ℂ f) : Differentiable ℂ (corrected τ hτ δ f) :=
  hf.mul ((((linear τ hτ δ).toContinuousLinearMap.differentiable.const_mul (Real.pi:ℂ)).neg).cexp)

/-- The exact flat translation character gives a unit-modulus residual
multiplier after the original Hermitian correction. -/
theorem correction_shift (δ : ComplexVectors) (f : ComplexVectors → ℂ)
    (hshift : ∀ (l : L τ hτ) z,
      f (z+l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f z)
    (l : L τ hτ) (z : ComplexVectors) :
    corrected τ hτ δ f (z+l.val)=corrected τ hτ δ f z*
      Complex.exp ((Real.pi:ℂ)*(form τ hτ δ l.val-form τ hτ l.val δ)) := by
  rw [corrected,corrected,hshift,form_add_left]
  have he : -((Real.pi:ℂ)*(form τ hτ z δ+form τ hτ l.val δ))=
      -((Real.pi:ℂ)*form τ hτ z δ)-((Real.pi:ℂ)*form τ hτ l.val δ) := by ring
  rw [he,Complex.exp_sub,mul_sub,Complex.exp_sub]
  ring

lemma correction_norm_periodic (δ : ComplexVectors) (f : ComplexVectors → ℂ)
    (hshift : ∀ (l : L τ hτ) z,
      f (z+l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f z)
    (l : L τ hτ) (z : ComplexVectors) :
    ‖corrected τ hτ δ f (z+l.val)‖=‖corrected τ hτ δ f z‖ := by
  rw [correction_shift τ hτ δ f hshift,norm_mul,Complex.norm_exp]
  have hr : ((Real.pi:ℂ)*(form τ hτ δ l.val-form τ hτ l.val δ)).re=0 := by
    rw [hermitian τ hτ δ l.val]
    simp only [Complex.star_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.sub_re,Complex.conj_re,sub_self,mul_zero,zero_mul,sub_zero]
  rw [hr,Real.exp_zero,mul_one]

/-- Compactness of the actual original torus and Liouville supply the
character, rather than assuming an entire logarithm or a linear exponent. -/
theorem exponential_character (δ : ComplexVectors) (f : ComplexVectors → ℂ)
    (hf : Differentiable ℂ f) (h0 : f 0≠0)
    (hshift : ∀ (l : L τ hτ) z,
      f (z+l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f z) :
    ∃ ℓ : ComplexVectors →ₗ[ℂ] ℂ, ∀ l : L τ hτ,
      Complex.exp (ℓ l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val) := by
  have hb : Bornology.IsBounded (Set.range (corrected τ hτ δ f)) := by
    apply CompactPeriodNormBound318.bounded_range (periodSubgroup representation order τ)
      (corrected τ hτ δ f) (correction_entire τ hτ δ f hf).continuous
    intro l z
    have hl : l.val ∈ L τ hτ := by
      change l.val ∈ lattice τ hτ
      rw [←exact_period_subgroup τ hτ]
      exact l.property
    exact correction_norm_periodic τ hτ δ f hshift ⟨l.val,hl⟩ z
  have he : ∀ z,corrected τ hτ δ f z=f 0 := by
    intro z
    have hc := (correction_entire τ hτ δ f hf).apply_eq_apply_of_bounded hb z 0
    simpa only [corrected,show form τ hτ 0 δ=0 from (linear τ hτ δ).map_zero,
      mul_zero,neg_zero,Complex.exp_zero,mul_one] using hc
  refine ⟨(Real.pi:ℂ) • linear τ hτ δ,?_⟩
  intro l
  have hc := he l.val
  have hs : f l.val=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f 0 := by
    simpa only [zero_add] using hshift l 0
  rw [corrected,hs] at hc
  have hmul := congrArg (fun w : ℂ => w*Complex.exp ((Real.pi:ℂ)*form τ hτ l.val δ)) hc
  simp only [Complex.exp_neg] at hmul
  have heq : Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f 0=
      f 0*Complex.exp ((Real.pi:ℂ)*form τ hτ l.val δ) := by
    simpa only [mul_assoc,inv_mul_cancel₀ (Complex.exp_ne_zero _),mul_one] using hmul
  change Complex.exp ((Real.pi:ℂ)*form τ hτ l.val δ)=_
  have heq' : f 0*Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)=
      f 0*Complex.exp ((Real.pi:ℂ)*form τ hτ l.val δ) :=
    (mul_comm _ _).trans heq
  exact (mul_left_cancel₀ h0 heq').symm

/-- Produced nonzero entire translation scalar forces membership in the
SAME original period lattice through its proved perfect pairing. -/
theorem original_period (δ : ComplexVectors) (f : ComplexVectors → ℂ)
    (hf : Differentiable ℂ f) (h0 : f 0≠0)
    (hshift : ∀ (l : L τ hτ) z,
      f (z+l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*f z) : δ∈L τ hτ := by
  obtain ⟨ℓ,hℓ⟩ := exponential_character τ hτ δ f hf h0 hshift
  exact PELOriginalExponentialLatticeCharacter318.period_of_character τ hτ δ ℓ hℓ
end PELOriginalEntireTranslationCharacter318
