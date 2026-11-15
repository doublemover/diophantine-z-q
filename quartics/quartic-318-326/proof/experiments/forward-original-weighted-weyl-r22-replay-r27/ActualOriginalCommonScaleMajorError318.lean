module
public import ActualOriginalFiniteMajorMassPolynomial318
public section
noncomputable section
namespace ActualOriginalCommonScaleMajorError318
open QuadricCRTAssembly318 ActualOriginalPolynomialMinorScale318 ActualOriginalPolynomialMinorDecay318
open ActualOriginalFlexibleMinorScale318 ActualOriginalFiniteMajorMassPolynomial318
open ActualOriginalFiniteMajorArcError318 ActualOriginalNonzeroModeSum318 Filter
open scoped ContDiff Topology

/-- The old fixed derivative exponent k is now absorbed by a concrete
polynomial scale p=k, rather than an uncontrolled diagonal. Both the
rational denominator cutoff and beta cutoff are the SAME N=n^8. -/
theorem actual_common_scale_major_error_bound (κ : ℕ) (hκ : 0<κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ p : ℕ, ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 2≤n →
      ‖finiteMajorArcError κ (minorCutoff n) (flexibleScale p n) (minorCutoff n : ℝ) W /
        (flexibleScale p n : ℂ)^3‖≤K/(n : ℝ)^2 := by
  obtain ⟨k,C,hC,hb⟩ := actual_finite_major_arc_error κ hκ W hW hc
  let K := C*(2 : ℝ)^k*2*latticeSixthMass*Real.sqrt (32*(κ : ℝ))
  have hL := latticeSixthMass_nonneg
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨k,K,hK,fun n hn => ?_⟩
  let N := minorCutoff n
  let B := flexibleScale k n
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hx : (0 : ℝ)<n := by linarith
  obtain ⟨hN,hB,hs⟩ := actual_flexible_minor_scale k n hn
  have hBp : 0<B := lt_of_lt_of_le (by norm_num) hB
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hmass := actual_finite_major_mass_polynomial κ N
  have hwindow : (1+(N : ℝ))^k≤(2*(N : ℝ))^k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have hprod := mul_le_mul hwindow hmass (finiteArcMass_nonneg κ N) (by positivity)
  have hfactor : 0≤C*(2*(N : ℝ))*latticeSixthMass := by positivity
  have hmajorant : C*(1+(N : ℝ))^k*(2*(N : ℝ))*latticeSixthMass*finiteArcMass κ N≤
      K*(n : ℝ)^(k*8+56) := by
    have hh := mul_le_mul_of_nonneg_left hprod hfactor
    dsimp only [K,N,minorCutoff] at hh ⊢
    push_cast at hh
    simp only [mul_pow,←pow_mul,Nat.mul_comm 8 k] at hh
    convert hh using 1 <;> simp only [mul_pow,pow_add,pow_mul] <;> ring
  have hraw := hb N B N hBp (Nat.cast_nonneg N)
  have hnorm : ‖finiteMajorArcError κ N B N W/(B : ℂ)^3‖≤
      K*(n : ℝ)^(k*8+56)/B^6 := by
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hBp]
    have hh := (div_le_div_of_nonneg_right hraw (pow_nonneg hBp.le 3)).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmajorant (pow_nonneg hBp.le 3))
        (pow_nonneg hBp.le 3))
    convert hh using 1 <;> field_simp [ne_of_gt hBp] <;> ring
  have hratio : (n : ℝ)^(k*8+56)/B^6≤1/(n : ℝ)^2 := by
    apply (div_le_div_iff₀ (pow_pos hBp 6) (sq_pos_of_pos hx)).mpr
    have hh := actual_power_degree_mono (n : ℝ) hx1 (k*8+58) (k*48+192) (by omega)
    dsimp only [B,flexibleScale]
    convert hh using 1 <;> simp only [pow_add,pow_mul] <;> ring
  apply hnorm.trans
  have hh := mul_le_mul_of_nonneg_left hratio hK
  simpa only [mul_div_assoc,mul_one] using hh

lemma actual_common_scale_major_error_limit (κ : ℕ) (hκ : 0<κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ p : ℕ, Tendsto (fun n : ℕ =>
      finiteMajorArcError κ (minorCutoff (n+2)) (flexibleScale p (n+2)) (minorCutoff (n+2) : ℝ) W /
        (flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 0) := by
  obtain ⟨p,K,hK,hb⟩ := actual_common_scale_major_error_bound κ hκ W hW hc
  exact ⟨p,squeeze_zero_norm (fun n => hb (n+2) (by omega)) (actual_polynomial_inverse_limit K)⟩

end ActualOriginalCommonScaleMajorError318
