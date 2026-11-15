module
public import ActualOriginalFlexibleMinorDecay318
public section
noncomputable section
namespace ActualOriginalFiniteMajorMassPolynomial318
open ActualOriginalFiniteMajorArcError318
open scoped BigOperators

/-- Every actual unit numerator is injected into the complete residue
ring. This includes modulus one and all even/bad-prime moduli. -/
lemma actual_unit_numerator_card (q : ℕ) [NeZero q] :
    Fintype.card {a : ZMod q // IsUnit a}≤q := by
  calc
    _ ≤ Fintype.card (ZMod q) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := ZMod.card q

lemma actual_one_modulus_mass (κ q : ℕ) [NeZero q] :
    (∑ _a : {a : ZMod q // IsUnit a}, Real.sqrt (32*(κ : ℝ)*(q : ℝ)^5)*(q : ℝ))≤
      Real.sqrt (32*(κ : ℝ))*(q : ℝ)^5 := by
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hpow := ActualOriginalPolynomialMinorScale318.actual_power_degree_mono (q : ℝ) hq1 5 6 (by omega)
  have hs : Real.sqrt ((q : ℝ)^5)≤(q : ℝ)^3 := by
    have hh := Real.sqrt_le_sqrt hpow
    rw [show (q : ℝ)^6=((q : ℝ)^3)^2 by ring,Real.sqrt_sq (by positivity)] at hh
    exact hh
  have hcard : (Fintype.card {a : ZMod q // IsUnit a} : ℝ)≤q := by
    exact_mod_cast actual_unit_numerator_card q
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Real.sqrt_mul (by positivity : 0≤32*(κ : ℝ))]
  have h1 := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (32*(κ : ℝ)))
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg q : (0 : ℝ)≤q)
  have h3 := mul_le_mul hcard h2 (by positivity) (by positivity)
  convert h3 using 1 <;> ring

/-- Quantitative replacement for the old merely finite arithmetic mass.
No good-modulus restriction or unproved totient asymptotic is introduced. -/
theorem actual_finite_major_mass_polynomial (κ N : ℕ) :
    finiteArcMass κ N≤Real.sqrt (32*(κ : ℝ))*(N : ℝ)^6 := by
  calc
    _ ≤ ∑ q : Fin N, Real.sqrt (32*(κ : ℝ))*((q.val+1 : ℕ) : ℝ)^5 := by
      apply Finset.sum_le_sum
      intro q hq
      exact actual_one_modulus_mass κ (q.val+1)
    _ ≤ ∑ _q : Fin N, Real.sqrt (32*(κ : ℝ))*(N : ℝ)^5 := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show q.val+1≤N by omega)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

end ActualOriginalFiniteMajorMassPolynomial318
