module
public import ActualGaussianWeberNamedPositivePeriodLift318
public import Mathlib.GroupTheory.OrderOfElement
public section
noncomputable section

namespace ActualGaussianWeberPositivePeriodAnnihilator318

open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberFullCoordinateField318 ActualGaussianWeberAlgebraicClosureTorsion318

attribute [local instance] Classical.decEq

/-- Exact annihilator of the actual positive point of the literal
square torus. This is a Gaussian ideal condition, not just an
integer-order estimate or a prime-fibre count. -/
theorem literal_positive_period_annihilator
    (n : ℕ) (hn : 0<n) (g : GaussianInt) :
    scalar g (V ((1:ℂ)/(n:ℂ)))=0 ↔ (n:GaussianInt)∣g := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  rw [scalar_on]
  constructor
  · intro h
    obtain ⟨z,hz⟩ := (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mp h
    change iota z=iota g*(1/(n:ℂ)) at hz
    have hz' : iota z=iota g/(n:ℂ) := by
      simpa only [one_div,div_eq_mul_inv] using hz
    refine ⟨z,iota.injective ?_⟩
    rw [map_mul,map_natCast]
    calc
      _ = (iota g/(n:ℂ))*(n:ℂ) := (div_mul_cancel₀ _ hnC).symm
      _ = iota z*(n:ℂ) := congrArg (fun u : ℂ => u*(n:ℂ)) hz'.symm
      _ = _ := mul_comm _ _
  · rintro ⟨z,rfl⟩
    rw [map_mul,map_natCast,mul_div_assoc,mul_one,mul_comm (n:ℂ),
      mul_div_cancel_right₀ _ hnC]
    exact (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mpr ⟨z,rfl⟩

/-- The same point in the original named field has exact additive
order n; any smaller annihilating multiple would already be in the
Gaussian lattice kernel above. The point is not reselected. -/
theorem old_positive_period_point_order
    (n : ℕ) (hn : 1<n) (P : WP (fullField Ω n)) (hT : n • P=0)
    (hImage : coordinateHom (chosenClosureEmbedding.comp (algebraMap (fullField Ω n) Ω))
        (by norm_num : (2:ℂ)≠0) P =
      ActualLSGOriginalFullUniformization318.uniformization.point (V ((1:ℂ)/(n:ℂ)))) :
    addOrderOf P=n := by
  let f : (fullField Ω n)→+*ℂ :=
    chosenClosureEmbedding.comp (algebraMap (fullField Ω n) Ω)
  let E := coordinateHom f (by norm_num : (2:ℂ)≠0)
  let U := ActualLSGOriginalFullUniformization318.uniformization.point
  let q := V ((1:ℂ)/(n:ℂ))
  have hIm : E P=U q := hImage
  have hn₀ : 0<n := Nat.zero_lt_one.trans hn
  apply (addOrderOf_eq_iff hn₀).mpr
  refine ⟨hT,?_⟩
  intro k hk hk₀ hK
  have hq : k • q=0 := by
    apply U.injective
    calc
      _ = k • U q := map_nsmul U q k
      _ = E (k • P) := by rw [←hIm,map_nsmul]
      _ = 0 := by rw [hK,map_zero]
      _ = _ := (map_zero U).symm
  have hG : scalar (k:GaussianInt) q=0 := by
    change scalar (k:GaussianInt) (V ((1:ℂ)/(n:ℂ)))=0
    rw [scalar_on,map_natCast,←nsmul_eq_mul,map_nsmul]
    exact hq
  obtain ⟨z,hz⟩ := (literal_positive_period_annihilator n hn₀ (k:GaussianInt)).mp hG
  have hdz : (n:ℤ)∣(k:ℤ) := by
    refine ⟨z.re,?_⟩
    simpa only [Zsqrtd.re_natCast,Zsqrtd.im_natCast,Zsqrtd.re_mul,zero_mul,
      mul_zero,add_zero] using congrArg (fun t : GaussianInt => t.re) hz
  exact (not_le_of_gt hk) (Nat.le_of_dvd hk₀ (Int.natCast_dvd_natCast.mp hdz))

end ActualGaussianWeberPositivePeriodAnnihilator318
