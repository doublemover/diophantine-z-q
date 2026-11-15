module
public import ActualOriginalIntegratedMinorMoment318
public section
noncomputable section
namespace ActualOriginalPolynomialMinorScale318
open ActualOriginalIntegratedMinorMoment318 ActualOriginalCanonicalOverlapLength318

/-- Explicit minor-only polynomial scale. Compatibility with the old
major-arc arbitrary-fast diagonal is NOT asserted by this definition. -/
@[expose] def minorCutoff (n : ℕ) : ℕ := n^8
@[expose] def minorScale (n : ℕ) : ℝ := (n : ℝ)^32
@[expose] def minorDivisorExponent : ℝ := 1/64

lemma actual_power_degree_mono (x : ℝ) (hx : 1≤x) (m n : ℕ) (hmn : m≤n) : x^m≤x^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  calc
    _ = x^m*1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ hx) (pow_nonneg (by linarith) _)

lemma actual_polynomial_minor_scale (n : ℕ) (hn : 2≤n) :
    0<minorCutoff n ∧ 1≤minorScale n ∧ ((minorCutoff n : ℝ)+1)^3≤minorScale n := by
  have hx : (2 : ℝ)≤n := by exact_mod_cast hn
  have hx1 : (1 : ℝ)≤n := by linarith
  have hx8 : (1 : ℝ)≤(n : ℝ)^8 := one_le_pow₀ hx1
  have hx8' : (8 : ℝ)≤(n : ℝ)^8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hx 8
    norm_num at hh
    linarith
  refine ⟨pow_pos (by omega) _,one_le_pow₀ hx1,?_⟩
  change (((n^8 : ℕ) : ℝ)+1)^3≤(n : ℝ)^32
  rw [Nat.cast_pow]
  calc
    _ ≤ (2*(n : ℝ)^8)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ = 8*(n : ℝ)^24 := by ring
    _ ≤ (n : ℝ)^8*(n : ℝ)^24 := mul_le_mul_of_nonneg_right hx8' (by positivity)
    _ = _ := by ring

lemma actual_polynomial_dirichlet_order (n : ℕ) (hn : 0<n) :
    ⌈(minorScale n)^2/(minorCutoff n : ℝ)⌉₊=n^56 := by
  have hx : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (minorScale n)^2/(minorCutoff n : ℝ)=((n^56 : ℕ) : ℝ) := by
    simp only [minorScale,minorCutoff,Nat.cast_pow]
    field_simp [hx]
    <;> ring
  rw [he]
  simp

lemma actual_polynomial_radius (R : ℝ) (hR : 1≤R) (n : ℕ) (hn : 2≤n) :
    (canonicalMomentRadius R (minorScale n) : ℝ)≤(R+1)*(n : ℝ)^32 := by
  have hB := (actual_polynomial_minor_scale n hn).2.1
  have hH := actual_scaled_radius_nonneg R (minorScale n) (by linarith) (by linarith)
  have he : (canonicalMomentRadius R (minorScale n) : ℤ)=⌈R*minorScale n⌉ := Int.toNat_of_nonneg hH
  have heR : (canonicalMomentRadius R (minorScale n) : ℝ)=(⌈R*minorScale n⌉ : ℝ) := by exact_mod_cast he
  rw [heR]
  have hh := Int.ceil_lt_add_one (R*minorScale n)
  dsimp only [minorScale] at hh hB
  nlinarith

end ActualOriginalPolynomialMinorScale318
