module
public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic
public section
noncomputable section

namespace ActualGaussianWeberHenselianChart318

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R]

/-- On the literal Weber cubic this is the normalized Y=1
chart, with homogeneous representative (-t : 1 : -w). -/
@[expose] def identityChart (t w : R) : Prop :=
  w + t * w^2 = t^3

theorem chart_turn (t w i : R) (hi : i^2 = -1) (h : identityChart t w) :
    identityChart (i*t) (-i*w) := by
  have hS : (-i*w)^2 = -(w^2) := by rw [mul_pow,neg_sq,hi,neg_one_mul]
  have hC : (i*t)^3 = -i*t^3 := by
    rw [mul_pow,show (3:ℕ)=2+1 by decide,pow_add,hi,pow_one,neg_one_mul]
  unfold identityChart at h ⊢
  rw [hS,hC]
  linear_combination -i*h

/-- The Y=1 equation determines the first-order coordinate with no
division and even when the coefficient ring has zero divisors. -/
theorem chart_squarezero {t w : R} (h : identityChart t w)
    (ht : t*t=0) (hw : w*w=0) : w=0 := by
  have ht3 : t^3=0 := by
    calc
      t^3 = (t*t)*t := by ring
      _ = 0 := by rw [ht,zero_mul]
  unfold identityChart at h
  have hw2 : w^2=0 := by simpa only [pow_two] using hw
  simpa only [hw2,mul_zero,add_zero,ht3] using h

section Local
variable [IsLocalRing R]

theorem chart_unique {t w v : R} (ht : t ∈ maximalIdeal R)
    (hw : identityChart t w) (hv : identityChart t v) : w=v := by
  have ht0 := (residue_eq_zero_iff t).mpr ht
  have hU : IsUnit (1+t*(w+v)) := (residue_ne_zero_iff_isUnit _).mp (by
    simp only [map_add,map_one,map_mul,ht0,zero_mul,add_zero]
    exact one_ne_zero)
  have he : (1+t*(w+v))*(w-v) = (1+t*(w+v))*0 := by
    unfold identityChart at hw hv
    linear_combination hw - hv
  exact sub_eq_zero.mp (hU.mul_left_cancel he)

/-- The actual chart Hensel lift uses the monic polynomial
rho^2+rho-t^4, not the nonmonic polynomial in w. No cancellation
of t and no nonzero assumption on t is used. -/
theorem chart_exists [HenselianLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    ∃! w : R, w ∈ maximalIdeal R ∧ identityChart t w := by
  let f : R[X] := X^2 + (X - C (t^4))
  have hdeg : (X - C (t^4)).degree < (2:WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_sub_le _ _)
    exact max_lt_iff.mpr ⟨by rw [degree_X]; decide,
      lt_of_le_of_lt degree_C_le (by decide)⟩
  have hf : f.Monic := monic_X_pow_add hdeg
  have h0 : f.eval (0:R) ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    have ht0 := (residue_eq_zero_iff t).mpr ht
    simp [f,ht0]
  have h1 : IsUnit (f.derivative.eval (0:R)) := by
    have hD : f.derivative.eval (0:R) = 1 := by
      change (X^2+(X-C (t^4)) : R[X]).derivative.eval (0:R) = 1
      rw [derivative_add,derivative_sub,derivative_C,derivative_X,derivative_X_pow]
      simp [show (2:ℕ)-1=1 by decide]
    rw [hD]
    exact isUnit_one
  obtain ⟨r,hr,hr0⟩ := HenselianLocalRing.is_henselian f hf (0:R) h0 h1
  have hrI : r ∈ maximalIdeal R := by simpa only [sub_zero] using hr0
  have hprod : r*(1+r)=t^4 := by
    have he := (IsRoot.def.mp hr)
    simp only [f,eval_add,eval_pow,eval_X,eval_sub,eval_C] at he
    linear_combination he
  have hrZ := (residue_eq_zero_iff r).mpr hrI
  have hU : IsUnit (1+r) := (residue_ne_zero_iff_isUnit _).mp (by
    simp only [map_add,map_one,hrZ,add_zero]
    exact one_ne_zero)
  obtain ⟨u,hu⟩ := hU
  let w : R := t^3 * ↑u⁻¹
  have hwU : w * (u:R) = t^3 := by
    change (t^3 * (↑u⁻¹:R)) * (u:R) = t^3
    rw [mul_assoc,u.inv_mul,mul_one]
  have htw : t*w=r := by
    apply u.isUnit.mul_right_cancel
    rw [mul_assoc,hwU,hu,hprod]
    ring
  have he : identityChart t w := by
    unfold identityChart
    calc
      w+t*w^2 = w*(1+r) := by rw [←htw]; ring
      _ = t^3 := by rw [←hu]; exact hwU
  have hwI : w ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    have ht0 := (residue_eq_zero_iff t).mpr ht
    simp [w,ht0]
  exact ⟨w,⟨hwI,he⟩,fun v hv => chart_unique ht hv.2 he⟩

/-- Exact algebra used by the [M]-expansion in the formal kernel.
The nonzero residue of M is essential (and sufficient for this step).
There is no completeness/domain or inverse-power-series premise. -/
theorem unit_linear_kernel (m t c : R)
    (hm : residue R m ≠ 0) (ht : t ∈ maximalIdeal R)
    (h : m*t+t^2*c=0) : t=0 := by
  have ht0 := (residue_eq_zero_iff t).mpr ht
  have hU : IsUnit (m+t*c) := (residue_ne_zero_iff_isUnit _).mp (by
    simpa only [map_add,map_mul,ht0,zero_mul,add_zero] using hm)
  apply hU.mul_left_cancel
  calc
    (m+t*c)*t = m*t+t^2*c := by ring
    _ = 0 := h
    _ = (m+t*c)*0 := (mul_zero _).symm

end Local
end ActualGaussianWeberHenselianChart318
