module
public import CanonicalCurveTrace318
public import Mathlib.Data.Nat.Prime.Int
public section
namespace GaussianNormUniqueness318
set_option maxHeartbeats 1000000

/-- An integral dot product of two vectors of the same prime norm,
if divisible by that norm, can only be zero or plus/minus the norm.
The zero case swaps the coordinate squares; the other two preserve them. -/
lemma squares_of_dot_divisible (p : ℕ) (hp : 0<p) (a b c d : ℤ)
    (ha : a^2+b^2=(p:ℤ)) (hc : c^2+d^2=(p:ℤ))
    (hdiv : (p:ℤ)∣a*c+b*d) : a^2=c^2 ∨ a^2=d^2 := by
  have hpz : (0:ℤ)<p := by exact_mod_cast hp
  have hpne : (p:ℤ)≠0 := ne_of_gt hpz
  have hsum : (a*c+b*d)^2+(a*d-b*c)^2=(p:ℤ)^2 := by
    calc
      _ = (a^2+b^2)*(c^2+d^2) := by ring
      _ = (p:ℤ)^2 := by rw [ha,hc]; ring
  obtain ⟨k,hk⟩ := hdiv
  have hbound : k^2*(p:ℤ)^2≤1*(p:ℤ)^2 := by
    rw [hk] at hsum
    nlinarith [sq_nonneg (a*d-b*c)]
  have hk2 : k^2≤1 := (mul_le_mul_right (sq_pos_of_pos hpz)).mp hbound
  have hlow : -1≤k := by nlinarith
  have hupp : k≤1 := by nlinarith
  have hcases : k= -1 ∨ k=0 ∨ k=1 := by omega
  have parallel : a*d-b*c=0 → a^2=c^2 := by
    intro hcross
    have he : (a^2-c^2)*(p:ℤ)=(a*d-b*c)*(a*d+b*c) := by
      linear_combination c^2*ha-a^2*hc
    rw [hcross,zero_mul] at he
    have hz := (mul_eq_zero.mp he).resolve_right hpne
    linarith
  rcases hcases with h|h|h
  · left
    apply parallel
    rw [h] at hk
    have hz : (a*d-b*c)^2=0 := by nlinarith
    nlinarith
  · right
    rw [h,mul_zero] at hk
    have he : (a^2-d^2)*(p:ℤ)=(a*c-b*d)*(a*c+b*d) := by
      linear_combination d^2*ha-a^2*hc
    rw [hk,mul_zero] at he
    have hz := (mul_eq_zero.mp he).resolve_right hpne
    linarith
  · left
    apply parallel
    rw [h,mul_one] at hk
    have hz : (a*d-b*c)^2=0 := by nlinarith
    nlinarith

/-- Prime divisibility and the norm identity give the same coordinate-square
alternatives as Gaussian unique factorization, with no assumed associate. -/
theorem coordinate_squares (p : ℕ) (hp : p.Prime) (a b c d : ℤ)
    (ha : a^2+b^2=(p:ℤ)) (hc : c^2+d^2=(p:ℤ)) :
    a^2=c^2 ∨ a^2=d^2 := by
  have hprod : (p:ℤ)∣(a*c+b*d)*(a*c-b*d) := by
    refine ⟨c^2-b^2,?_⟩
    linear_combination c^2*ha-b^2*hc
  have hpint : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpint.2.2 _ _ hprod with h|h
  · exact squares_of_dot_divisible p hp.pos a b c d ha hc h
  · have hc' : c^2+(-d)^2=(p:ℤ) := by simpa only [neg_sq] using hc
    have hd : (p:ℤ)∣a*c+b*(-d) := by simpa only [mul_neg,←sub_eq_add_neg] using h
    simpa only [neg_sq] using squares_of_dot_divisible p hp.pos a b c (-d) ha hc' hd

/-- The odd-real/even-imaginary condition excludes the imaginary Gaussian
associates explicitly, including negative coordinates. -/
theorem odd_real_square (p : ℕ) (hp : p.Prime) (a b c d : ℤ)
    (ha : a^2+b^2=(p:ℤ)) (hc : c^2+d^2=(p:ℤ))
    (hb : b%2=0) (hcod : c%2=1) : a^2=c^2 := by
  rcases coordinate_squares p hp a b c d ha hc with h|h
  · exact h
  · have he : c^2=b^2 := by nlinarith
    have hmod := congrArg (fun z : ℤ => z%2) he
    norm_num [Int.pow_emod,hb,hcod] at hmod

end GaussianNormUniqueness318
