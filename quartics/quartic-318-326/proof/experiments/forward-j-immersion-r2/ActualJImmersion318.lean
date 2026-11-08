module
public import OpenJLocalComparison318
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula
public import FiniteAnalyticCharts318
public section
noncomputable section
open Filter Set
open scoped Topology Manifold
namespace ActualJImmersion318
open OpenJComplexEvaluation318 OpenJLocalComparison318
set_option maxHeartbeats 0

lemma two_pi_I_ne_zero : (2*(Real.pi:ℂ)*Complex.I)≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

lemma derivative_E4 (tau : UpperHalfPlane) :
    deriv (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ)=
      (2*(Real.pi:ℂ)*Complex.I)*(EisensteinSeries.E2 tau*ModularForm.E₄ tau-
        ModularForm.E₆ tau)/3 := by
  have h := congrFun Derivative.normalizedDerivOfComplex_E₄ tau
  change (2*(Real.pi:ℂ)*Complex.I)⁻¹*
    deriv (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ)=
      (3:ℂ)⁻¹*(EisensteinSeries.E2 tau*ModularForm.E₄ tau-ModularForm.E₆ tau) at h
  calc
    _=(2*(Real.pi:ℂ)*Complex.I)*((2*(Real.pi:ℂ)*Complex.I)⁻¹*
      deriv (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ)) := by
        field_simp [two_pi_I_ne_zero]
    _=_ := by rw [h]; ring

lemma derivative_E6 (tau : UpperHalfPlane) :
    deriv (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ)=
      (2*(Real.pi:ℂ)*Complex.I)*(EisensteinSeries.E2 tau*ModularForm.E₆ tau-
        ModularForm.E₄ tau^2)/2 := by
  have h := congrFun Derivative.normalizedDerivOfComplex_E₆ tau
  change (2*(Real.pi:ℂ)*Complex.I)⁻¹*
    deriv (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ)=
      (2:ℂ)⁻¹*(EisensteinSeries.E2 tau*ModularForm.E₆ tau-ModularForm.E₄ tau^2) at h
  calc
    _=(2*(Real.pi:ℂ)*Complex.I)*((2*(Real.pi:ℂ)*Complex.I)⁻¹*
      deriv (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ)) := by
        field_simp [two_pi_I_ne_zero]
    _=_ := by rw [h]; ring

/-- The exact derivative of the genuine analytic j, from the actual normalized
Eisenstein series and discriminant. No unramifiedness premise is supplied. -/
theorem hasDerivAt_j (tau : UpperHalfPlane) :
    HasDerivAt j (-(2*(Real.pi:ℂ)*Complex.I)*ModularForm.E₄ tau^2*
      ModularForm.E₆ tau/ModularForm.discriminant tau) (tau:ℂ) := by
  have ha : HasDerivAt (fun z : ℂ => ModularForm.E₄ (UpperHalfPlane.ofComplex z))
      (deriv (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (tau:ℂ)) (tau:ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₄.holo' tau)).hasDerivAt
  have hb : HasDerivAt (fun z : ℂ => ModularForm.E₆ (UpperHalfPlane.ofComplex z))
      (deriv (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (tau:ℂ)) (tau:ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₆.holo' tau)).hasDerivAt
  rw [derivative_E4] at ha
  rw [derivative_E6] at hb
  have hd := ((ha.pow 3).sub (hb.pow 2)).div_const (1728:ℂ)
  change HasDerivAt (fun z : ℂ => (ModularForm.E₄ (UpperHalfPlane.ofComplex z)^3-
    ModularForm.E₆ (UpperHalfPlane.ofComplex z)^2)/1728) _ _ at hd
  have hfun : (fun z : ℂ => (ModularForm.E₄ (UpperHalfPlane.ofComplex z)^3-
      ModularForm.E₆ (UpperHalfPlane.ofComplex z)^2)/1728)=
      (fun z => ModularForm.discriminant (UpperHalfPlane.ofComplex z)) := by
    funext z
    exact (ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq _).symm
  rw [hfun] at hd
  have hd' : HasDerivAt (fun z => ModularForm.discriminant (UpperHalfPlane.ofComplex z))
      ((2*(Real.pi:ℂ)*Complex.I)*EisensteinSeries.E2 tau*ModularForm.discriminant tau)
      (tau:ℂ) := by
    convert hd using 1
    simp only [UpperHalfPlane.ofComplex_apply]
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have hj := (ha.pow 3).div hd' (by
    simpa only [UpperHalfPlane.ofComplex_apply] using ModularForm.discriminant_ne_zero tau)
  convert hj using 1
  · funext z
    rfl
  · simp only [UpperHalfPlane.ofComplex_apply]
    field_simp [ModularForm.discriminant_ne_zero tau]
    ring

lemma E4_ne_zero (tau : UpperHalfPlane) (ht : Admissible tau) : ModularForm.E₄ tau≠0 := by
  intro hz
  apply ht.1
  simp [ActualQJ318.jInvariant,hz]

lemma E6_ne_zero (tau : UpperHalfPlane) (ht : Admissible tau) : ModularForm.E₆ tau≠0 := by
  intro hz
  apply ht.2
  have hd := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq tau
  rw [hz,zero_pow (by decide : 2≠0),sub_zero] at hd
  change ModularForm.E₄ tau^3/ModularForm.discriminant tau=1728
  rw [hd]
  field_simp [E4_ne_zero tau ht]

/-- Genuine j is unramified at every point of the actual admissible locus. -/
theorem deriv_j_ne_zero (tau : UpperHalfPlane) (ht : Admissible tau) : deriv j (tau:ℂ)≠0 := by
  rw [(hasDerivAt_j tau).deriv]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_pi_I_ne_zero)
    (pow_ne_zero 2 (E4_ne_zero tau ht))) (E6_ne_zero tau ht))
      (ModularForm.discriminant_ne_zero tau)

/-- An actual local holomorphic inverse to the genuine j-function through every
admissible period. This inverse is proved from its computed nonzero derivative. -/
theorem exists_j_inverse (tau : UpperHalfPlane) (ht : Admissible tau) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (ActualQJ318.jInvariant tau) ∧
      g (ActualQJ318.jInvariant tau)=(tau:ℂ) ∧
      (fun z => g (j z)) =ᶠ[𝓝 (tau:ℂ)] id ∧
      (fun z => j (g z)) =ᶠ[𝓝 (ActualQJ318.jInvariant tau)] id := by
  simpa only [j,UpperHalfPlane.ofComplex_apply] using
    FiniteAnalyticCharts318.analytic_inverse (j_analyticAt tau) (deriv_j_ne_zero tau ht)

end ActualJImmersion318
