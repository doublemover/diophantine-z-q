module
public import ActualOriginalPolynomialMinorDecay318
public section
noncomputable section
namespace ActualOriginalFlexibleMinorScale318
open ActualOriginalPolynomialMinorScale318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalCanonicalOverlapLength318

/-- A fixed parameter p permits the SAME cutoff to be paired with a
larger polynomial scale. It is chosen before the sequence index n. -/
@[expose] def flexibleScale (p n : ℕ) : ℝ := (n : ℝ)^(p*8+32)
@[expose] def flexibleDivisorExponent (p : ℕ) : ℝ := 1/((p : ℝ)*16+64)
lemma actual_flexible_exponent_pos (p : ℕ) : 0<flexibleDivisorExponent p := by
  unfold flexibleDivisorExponent
  positivity

lemma actual_flexible_minor_scale (p n : ℕ) (hn : 2≤n) :
    0<minorCutoff n ∧ 1≤flexibleScale p n ∧ ((minorCutoff n : ℝ)+1)^3≤flexibleScale p n := by
  obtain ⟨hN,hB,hs⟩ := actual_polynomial_minor_scale n hn
  have hx : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hh := actual_power_degree_mono (n : ℝ) hx 32 (p*8+32) (by omega)
  exact ⟨hN,hB.trans hh,hs.trans hh⟩

lemma actual_flexible_dirichlet_order (p n : ℕ) (hn : 0<n) :
    ⌈(flexibleScale p n)^2/(minorCutoff n : ℝ)⌉₊=n^(p*16+56) := by
  have hx : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (flexibleScale p n)^2/(minorCutoff n : ℝ)=((n^(p*16+56) : ℕ) : ℝ) := by
    simp only [flexibleScale,minorCutoff,Nat.cast_pow,pow_add,pow_mul]
    field_simp [hx]
    <;> ring
  rw [he]
  simp

lemma actual_flexible_radius (R : ℝ) (hR : 1≤R) (p n : ℕ) (hn : 2≤n) :
    (canonicalMomentRadius R (flexibleScale p n) : ℝ)≤(R+1)*(n : ℝ)^(p*8+32) := by
  have hB := (actual_flexible_minor_scale p n hn).2.1
  have hH := actual_scaled_radius_nonneg R (flexibleScale p n) (by linarith) (by linarith)
  have he : (canonicalMomentRadius R (flexibleScale p n) : ℤ)=⌈R*flexibleScale p n⌉ := Int.toNat_of_nonneg hH
  have heR : (canonicalMomentRadius R (flexibleScale p n) : ℝ)=(⌈R*flexibleScale p n⌉ : ℝ) := by exact_mod_cast he
  rw [heR]
  have hh := Int.ceil_lt_add_one (R*flexibleScale p n)
  dsimp only [flexibleScale] at hh hB
  nlinarith

end ActualOriginalFlexibleMinorScale318
