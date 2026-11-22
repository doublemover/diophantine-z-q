module
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic
public section
noncomputable section

namespace ActualGaussianWeberRationalDerivativeCap318

open Polynomial

variable {K : Type*} [Field K]

/-- An exact consequence of clearing the denominator in r′=0. -/
theorem derivative_zero_of_coprime_cross {A B : K[X]} (hAB : IsCoprime A B)
    (h : A.derivative * B = A * B.derivative) :
    A.derivative = 0 ∧ B.derivative = 0 := by
  have hA : A ∣ A.derivative * B := ⟨B.derivative,h⟩
  have hB : B ∣ B.derivative * A := by
    refine ⟨A.derivative,?_⟩
    calc
      B.derivative * A = A * B.derivative := mul_comm _ _
      _ = A.derivative * B := h.symm
      _ = B * A.derivative := mul_comm _ _
  exact ⟨dvd_derivative_iff.mp (hAB.dvd_of_dvd_mul_right hA),
    dvd_derivative_iff.mp (hAB.symm.dvd_of_dvd_mul_right hB)⟩

theorem coeff_zero_inside {p : ℕ} [CharP K p] (A : K[X])
    (hA : A.derivative = 0) {n : ℕ} (hn : 0 < n) (hpn : n < p) :
    A.coeff n = 0 := by
  have hc : (n : K) ≠ 0 := by
    intro H
    exact (not_le_of_gt hpn) (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K p n).mp H))
  have he : (n-1)+1 = n := by omega
  have h := coeff_derivative A (n-1)
  rw [hA,coeff_zero,he] at h
  have hcast : (((n-1)+1 : ℕ) : K) ≠ 0 := by simpa only [he] using hc
  have hsum : ((n-1 : ℕ) : K)+1 ≠ 0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hcast
  exact (mul_eq_zero.mp h.symm).resolve_right hsum

/-- The literal degree ≤p bound and zero derivative leave only exponents 0 and p. -/
theorem capped_polynomial {p : ℕ} [CharP K p] (hp : 0 < p) (A : K[X])
    (hA : A.derivative = 0) (hdeg : A.natDegree ≤ p) :
    A = C (A.coeff 0) + C (A.coeff p) * X^p := by
  ext n
  rw [coeff_add,coeff_C,coeff_C_mul_X_pow]
  by_cases h0 : n = 0
  · subst n
    simp [hp.ne',Ne.symm hp.ne']
  by_cases hN : n = p
  · subst n
    simp [hp.ne',Ne.symm hp.ne']
  have hz : A.coeff n = 0 := by
    rcases lt_or_gt_of_ne hN with hlt | hgt
    · exact coeff_zero_inside A hA (Nat.pos_of_ne_zero h0) hlt
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hgt)
  simp [h0,hN,Ne.symm h0,Ne.symm hN,hz]

/-- Apply to a nonconstant rational map with a pole at infinity.
The pole gives deg B<deg A, so B is literally a constant. -/
theorem pole_forces_affine_frobenius {p : ℕ} [CharP K p] (hp : 0 < p)
    {A B : K[X]} (hAB : IsCoprime A B) (hB0 : B ≠ 0)
    (hd : B.natDegree < A.natDegree) (hcap : A.natDegree ≤ p)
    (hc : A.derivative * B = A * B.derivative) :
    A = C (A.coeff 0) + C (A.coeff p) * X^p ∧
      B = C (B.coeff 0) ∧ A.coeff p ≠ 0 ∧ B.coeff 0 ≠ 0 := by
  obtain ⟨hA,hB⟩ := derivative_zero_of_coprime_cross hAB hc
  have hNA := capped_polynomial hp A hA hcap
  have hb : B.natDegree < p := hd.trans_le hcap
  have hnB : B = C (B.coeff 0) := by
    have hBcap := capped_polynomial hp B hB hb.le
    simpa only [coeff_eq_zero_of_natDegree_lt hb,map_zero,zero_mul,add_zero] using hBcap
  refine ⟨hNA,hnB,?_,?_⟩
  · intro hz
    have h : A = C (A.coeff 0) := by simpa only [hz,map_zero,zero_mul,add_zero] using hNA
    have hA0 : A.natDegree = 0 := by rw [h,natDegree_C]
    omega
  · intro hz
    apply hB0
    simpa only [hz,map_zero] using hnB

end ActualGaussianWeberRationalDerivativeCap318
