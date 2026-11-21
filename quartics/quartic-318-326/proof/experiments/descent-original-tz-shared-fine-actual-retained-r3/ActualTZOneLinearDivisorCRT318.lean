module
public import ActualTZResidueIntervalCount318
public section
noncomputable section
namespace ActualTZOneLinearDivisorCRT318
open scoped BigOperators
open ActualTZResidueIntervalCount318

/-- Integral Bezout root for a good modulus, without assuming q prime
or choosing an inverse in a field. Works for the modulus-one branch. -/
theorem bezout_class (W q : ℕ) (c x : ℤ) (hc : W.Coprime q) :
    ((q:ℤ)∣(W:ℤ)*x+c) ↔ Int.ModEq (q:ℤ) (-Nat.gcdA W q*c) x := by
  let A := Nat.gcdA W q
  let B := Nat.gcdB W q
  have hbez : (W:ℤ)*A+(q:ℤ)*B=1 := by
    simpa only [A,B,hc.gcd_eq_one,Nat.cast_one] using (Nat.gcd_eq_gcd_ab W q).symm
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    obtain ⟨u,hu⟩ := h
    refine ⟨A*u+B*x,?_⟩
    change x-(-A*c)=(q:ℤ)*(A*u+B*x)
    linear_combination A*hu-x*hbez
  · intro h
    obtain ⟨u,hu⟩ := h
    refine ⟨(W:ℤ)*u+B*c,?_⟩
    change x-(-A*c)=(q:ℤ)*u at hu
    linear_combination (W:ℤ)*hu-c*hbez

/-- If a divisor has a prime in common with W, it never divides a
literal physical output W*(x+a)+b with b a unit modulo W. -/
theorem noncoprime_no_hit (W q b : ℕ) (hWb : W.Coprime b)
    (h : ¬ W.Coprime q) (x a : ℤ) :
    ¬(q:ℤ)∣(W:ℤ)*(x+a)+(b:ℤ) := by
  intro hhit
  let g := W.gcd q
  have hgW : g∣W := Nat.gcd_dvd_left _ _
  have hgq : g∣q := Nat.gcd_dvd_right _ _
  have hgWz : (g:ℤ)∣(W:ℤ) := by exact_mod_cast hgW
  have hgqz : (g:ℤ)∣(q:ℤ) := by exact_mod_cast hgq
  have hgBz := dvd_sub (hgqz.trans hhit) (dvd_mul_of_dvd_left hgWz (x+a))
  have hgB : g∣b := by
    exact_mod_cast (show (g:ℤ)∣(b:ℤ) by simpa only [add_sub_cancel_left] using hgBz)
  exact h (Nat.eq_one_of_dvd_coprimes hWb hgW hgB)

def count (W q b L : ℕ) (s a : ℤ) : ℕ :=
  ∑ t∈Finset.range L,if (q:ℤ)∣(W:ℤ)*(s+(t:ℤ)+a)+(b:ℤ) then 1 else 0

def localDensity (W q : ℕ) : ℝ := if W.Coprime q then 1/(q:ℝ) else 0

theorem count_good (W q b L : ℕ) (s a : ℤ) (hc : W.Coprime q) :
    count W q b L s a =
      intHits q L s (-Nat.gcdA W q*((W:ℤ)*a+(b:ℤ))) := by
  unfold count intHits
  apply Finset.sum_congr rfl
  intro t _
  have he : (W:ℤ)*(s+(t:ℤ)+a)+(b:ℤ)=(W:ℤ)*(s+(t:ℤ))+((W:ℤ)*a+(b:ℤ)) := by ring
  rw [he]
  have hiff : ((q:ℤ)∣(W:ℤ)*(s+(t:ℤ))+((W:ℤ)*a+(b:ℤ))) ↔
      Int.ModEq (q:ℤ) (s+(t:ℤ)) (-Nat.gcdA W q*((W:ℤ)*a+(b:ℤ))) :=
    (bezout_class W q _ _ hc).trans ⟨Int.ModEq.symm,Int.ModEq.symm⟩
  simp only [hiff]

theorem count_bad (W q b L : ℕ) (s a : ℤ) (hWb : W.Coprime b) (h : ¬ W.Coprime q) :
    count W q b L s a=0 := by
  simp only [count,if_neg (noncoprime_no_hit W q b hWb h _ _),Finset.sum_const_zero]

theorem density_nonneg (W q : ℕ) : 0≤localDensity W q := by
  unfold localDensity
  split_ifs <;> positivity

/-- Uniform unit-residue count on an arbitrary shifted wrap cell, with
an absolute raw rounding error at most one. -/
theorem count_density_error (W q b L : ℕ) (s a : ℤ) (hq : 0<q) (hWb : W.Coprime b) :
    |(count W q b L s a:ℝ)-(L:ℝ)*localDensity W q| ≤ 1 := by
  by_cases h : W.Coprime q
  · rw [count_good _ _ _ _ _ _ h,localDensity,if_pos h,mul_one_div]
    exact int_count_error q L _ _ hq
  · simp only [count_bad _ _ _ _ _ _ hWb h,Nat.cast_zero,localDensity,if_neg h,mul_zero,
      sub_zero,abs_zero,zero_le_one]

theorem normalized_error (W q b L : ℕ) (s a : ℤ) (hq : 0<q) (hWb : W.Coprime b)
    (hL : 0<L) :
    |(count W q b L s a:ℝ)/(L:ℝ)-localDensity W q| ≤ 1/(L:ℝ) := by
  have hLR : (0:ℝ)<L := by exact_mod_cast hL
  have he : (count W q b L s a:ℝ)/(L:ℝ)-localDensity W q =
      ((count W q b L s a:ℝ)-(L:ℝ)*localDensity W q)/(L:ℝ) := by
    field_simp [hLR.ne'] <;> ring
  rw [he,abs_div,abs_of_nonneg hLR.le]
  exact div_le_div_of_nonneg_right (count_density_error W q b L s a hq hWb) hLR.le

/-- On complete periods the ratio is the exact finite local factor.
This does not evaluate an Euler product as the cutoff grows. -/
theorem exact_full_period (W q b L : ℕ) (s a : ℤ) (hq : 0<q)
    (hWb : W.Coprime b) (hL : 0<L) (hm : q∣L) :
    (count W q b L s a:ℝ)/(L:ℝ)=localDensity W q := by
  by_cases h : W.Coprime q
  · have hqR : (0:ℝ)<q := by exact_mod_cast hq
    have hLR : (0:ℝ)<L := by exact_mod_cast hL
    rw [count_good _ _ _ _ _ _ h,exact_int_count _ _ _ _ hq,localDensity,if_pos h,
      Nat.mod_eq_zero_of_dvd hm,if_neg (Nat.not_lt_zero _),add_zero]
    apply (div_eq_div_iff hLR.ne' hqR.ne').2
    rw [one_mul]
    exact_mod_cast (Nat.div_mul_cancel hm)
  · simp only [count_bad _ _ _ _ _ _ hWb h,Nat.cast_zero,zero_div,localDensity,if_neg h]

theorem localDensity_pos (W q : ℕ) (hq : 0<q) (h : W.Coprime q) :
    0<localDensity W q := by
  rw [localDensity,if_pos h]
  positivity

end ActualTZOneLinearDivisorCRT318
