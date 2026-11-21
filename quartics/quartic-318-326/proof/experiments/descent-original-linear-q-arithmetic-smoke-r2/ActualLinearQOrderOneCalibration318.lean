module
public import ActualLinearQArithmeticCalibration318
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
noncomputable section
namespace ActualLinearQOrderOneCalibration318

open ActualLinearQArithmeticCalibration318
variable (p : ℕ) [Fact p.Prime]

private theorem nat_unit (n : ℕ) (hn : 0 < n) (h : n < p) :
    padicValRat p (n:ℚ) = 0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd
    (fun H => (not_le_of_gt h) (Nat.le_of_dvd hn H))] <;> rfl

private theorem negative_shift (x y : ℚ) (hx : x ≠ 0) (hxv : padicValRat p x = -1)
    (hy : 0 ≤ padicValRat p y) :
    x+y ≠ 0 ∧ padicValRat p (x+y) = -1 := by
  have hxy : x+y ≠ 0 := by
    intro hz
    have e : x = -y := by linarith
    rw [e,padicValRat.neg] at hxv
    omega
  by_cases hz : y = 0
  · subst y
    simpa only [add_zero] using And.intro hx hxv
  · exact ⟨hxy,(padicValRat.add_eq_of_lt hxy hx hz (by omega)).trans hxv⟩

/-- Exact contact and Delta at the extra denominator prime, derived
from the five literal rational roots (no hypothetical contact product). -/
theorem contact_delta (hb : 2399 < p) (c u A : ℚ)
    (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0)
    (hc0 : padicValRat p c = 0) (hu0 : padicValRat p u = 0) (hA0 : padicValRat p A = 0) :
    contact (parameter c u A p) ≠ 0 ∧
    padicValRat p (contact (parameter c u A p)) = -5 ∧
    delta c u A p ≠ 0 ∧ padicValRat p (delta c u A p) = -1 := by
  have hp : p.Prime := Fact.out
  have hpn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hP : padicValRat p (p:ℚ) = 1 := padicValRat.self hp.one_lt
  let T := parameter c u A p
  have hDen : A^2*(p:ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hA) hpn
  have hT : T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) (div_ne_zero hu hDen)
  have hv : padicValRat p T = -1 := by
    dsimp only [T,parameter,time]
    rw [padicValRat.mul (pow_ne_zero 2 hc) (div_ne_zero hu hDen),
      padicValRat.div hu hDen,padicValRat.mul (pow_ne_zero 2 hA) hpn,
      padicValRat.pow,padicValRat.pow,hc0,hu0,hA0,hP] <;> norm_num
  have h2 := nat_unit p 2 (by decide) (by omega)
  have h2399 := nat_unit p 2399 (by decide) hb
  have h32 := nat_unit p 32 (by decide) (by omega)
  have h407 := nat_unit p 407 (by decide) (by omega)
  have hs₁ : 0 ≤ padicValRat p (1/2:ℚ) := by
    rw [padicValRat.div (by decide : (1:ℚ) ≠ 0) (by decide : (2:ℚ) ≠ 0),padicValRat.one,h2] <;> norm_num
  have hs₃ : 0 ≤ padicValRat p (-(1/2399):ℚ) := by
    rw [padicValRat.neg,padicValRat.div (by decide : (1:ℚ) ≠ 0) (by decide : (2399:ℚ) ≠ 0),padicValRat.one,h2399] <;> norm_num
  have hs₄ : 0 ≤ padicValRat p (32/407:ℚ) := by
    rw [padicValRat.div (by decide : (32:ℚ) ≠ 0) (by decide : (407:ℚ) ≠ 0),h32,h407] <;> norm_num
  obtain ⟨ha,haV⟩ := negative_shift p T (1/2) hT hv hs₁
  obtain ⟨hb',hbV⟩ := negative_shift p T 1 hT hv (by rw [padicValRat.one] <;> exact le_rfl)
  obtain ⟨hd,hdV⟩ := negative_shift p T (-(1/2399)) hT hv hs₃
  obtain ⟨he,heV⟩ := negative_shift p T (32/407) hT hv hs₄
  obtain ⟨hD,hDV⟩ := negative_shift p T (-1) hT hv (by rw [padicValRat.neg,padicValRat.one] <;> exact le_rfl)
  have hF : contact T ≠ 0 := by
    simpa only [contact,sub_eq_add_neg] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hT ha) hb') hd) he
  have hFV : padicValRat p (contact T) = -5 := by
    simp only [contact,sub_eq_add_neg]
    rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hT ha) hb') hd) he,
      padicValRat.mul (mul_ne_zero (mul_ne_zero hT ha) hb') hd,
      padicValRat.mul (mul_ne_zero hT ha) hb',padicValRat.mul hT ha,hv,haV,hbV,hdV,heV] <;> norm_num
  exact ⟨hF,hFV,by simpa only [delta,T,sub_eq_add_neg] using hD,
    by simpa only [delta,T,sub_eq_add_neg] using hDV⟩

/-- Actual source numerical tuple (3,3,3,+1) at the order-only prime.
Only the independently produced unit trace value remains a premise. -/
theorem order_only_q (hb : 2399 < p) (τ c u A : ℚ)
    (hτ : τ ≠ 0) (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0)
    (hτ0 : padicValRat p τ = 0) (hc0 : padicValRat p c = 0)
    (hu0 : padicValRat p u = 0) (hA0 : padicValRat p A = 0) :
    padicValRat p (weight c u A p) = 3 ∧
    padicValRat p ((weight c u A p)^7*(delta c u A p)^18) = 3 ∧
    padicValRat p ((weight c u A p)^25*(delta c u A p)^72) = 3 ∧
    padicValRat p (pole τ c u A p) = 1 := by
  obtain ⟨hF,hFV,hΔ,hΔV⟩ := contact_delta p hb c u A hc hu hA hc0 hu0 hA0
  have hW : weight c u A p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF)
  have hWV : padicValRat p (weight c u A p) = 3 := by
    rw [weight,padicValRat.mul (pow_ne_zero _ hc) (div_ne_zero (pow_ne_zero _ hΔ) hF),
      padicValRat.div (pow_ne_zero _ hΔ) hF,padicValRat.pow,padicValRat.pow,hc0,hΔV,hFV] <;> norm_num
  refine ⟨hWV,?_,?_,?_⟩
  · rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
      padicValRat.pow,padicValRat.pow,hWV,hΔV] <;> norm_num
  · rw [padicValRat.mul (pow_ne_zero _ hW) (pow_ne_zero _ hΔ),
      padicValRat.pow,padicValRat.pow,hWV,hΔV] <;> norm_num
  · rw [pole,padicValRat.div (mul_ne_zero (pow_ne_zero _ hτ) hF)
      (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hΔ)),
      padicValRat.mul (pow_ne_zero _ hτ) hF,padicValRat.mul (pow_ne_zero _ hc) (pow_ne_zero _ hΔ),
      padicValRat.pow,padicValRat.pow,padicValRat.pow,hτ0,hc0,hFV,hΔV] <;> norm_num

end ActualLinearQOrderOneCalibration318
