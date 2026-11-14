module
public import ActualOriginalMajorArcUnionIntegral318
public section
noncomputable section
namespace ActualOriginalCircleMinorArcIdentity318
open QuadricCRTAssembly318 ActualOriginalMajorArcDomain318 ActualOriginalMajorArcIntegral318
open ActualOriginalMajorArcUnionIntegral318 ActualOriginalCompactCircleCount318
open ActualOriginalScaledCircle318 ActualOriginalFiniteCircleIdentity318
open MeasureTheory Filter
open scoped BigOperators Topology
set_option maxHeartbeats 16000000

/-- The original full circle count is independent of the chosen genuine
length-one fundamental interval. This follows from finite original Fourier
orthogonality, not from an assumed periodic-integral formula. -/
theorem actual_shifted_circle_count (κ : ℤ) (B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) (t : ℝ) :
    (∫ θ : ℝ in t..t+1, scaledCircleSum κ θ B W) = compactZeroCount κ B W := by
  obtain ⟨s,hs⟩ := actual_weight_finite_support B hB W hW
  simp_rw [actual_circle_eq_finite κ B W s hs]
  have he := fourierCoeff_eq_intervalIntegral (originalCircleSum κ s (latticeWeight B W)) 0 t
  have hc := actual_original_circle_coefficient κ s (latticeWeight B W)
  rw [he] at hc
  rw [actual_zero_count_eq_finite κ B W s hs]
  simpa only [neg_zero,fourier_zero,one_smul,div_one] using hc

@[expose] def minorArcIntegral (κ : ℤ) (N : ℕ) (B : ℝ)
    (W : Coordinates ℝ → ℝ) : ℂ :=
  ∫ θ in minorDomain N B, scaledCircleSum κ θ B W

/-- Exact major/minor decomposition on ACTUAL measurable domains. The
minor term is the literal complement in the shifted fundamental interval,
not a symbol defined as count minus a proposed main term. -/
theorem actual_major_plus_minor_count (κ : ℤ) (N : ℕ) (hN : 0 < N)
    (B : ℝ) (hB : 0 < B) (hscale : ((N : ℝ)+1)^3 ≤ B)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    majorArcIntegral κ N B (N : ℝ) W + minorArcIntegral κ N B W = compactZeroCount κ B W := by
  have hc := actual_scaled_circle_continuous κ B hB.ne' W hW
  have hi : IntegrableOn (fun θ => scaledCircleSum κ θ B W) (fundamental N B) :=
    hc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have he := integral_inter_add_sdiff (major_measurable N B) hi
  have hs : fundamental N B ∩ majorDomain N B = majorDomain N B :=
    Set.inter_eq_right.mpr (major_subset_fundamental N hN B hB hscale)
  rw [hs,actual_major_union_integral κ N B hB hscale W hW] at he
  change majorArcIntegral κ N B (N : ℝ) W+minorArcIntegral κ N B W=_ at he
  rw [he]
  have hf := actual_shifted_circle_count κ B hB.ne' W hW (-radius N B)
  rw [intervalIntegral.integral_of_le (by linarith)] at hf
  simpa only [fundamental,sub_eq_add_neg,add_comm] using hf

/-- The only analytic input still needed for the full asymptotic is the
stated limit of the ACTUAL complementary-domain integral. This theorem
does not assert or hide that missing minor-arc estimate. -/
theorem actual_count_limit_of_minor_limit (κ : ℤ) (B : ℕ → ℝ)
    (hB : ∀ n, 0 < B n) (hscale : ∀ n, ((n : ℝ)+1)^3 ≤ B n)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) (S : ℂ)
    (hmajor : Tendsto (fun n => majorArcIntegral κ n (B n) (n : ℝ) W/(B n : ℂ)^3)
      atTop (𝓝 S))
    (hminor : Tendsto (fun n => minorArcIntegral κ n (B n) W/(B n : ℂ)^3)
      atTop (𝓝 0)) :
    Tendsto (fun n => compactZeroCount κ (B n) W/(B n : ℂ)^3) atTop (𝓝 S) := by
  have he : (fun n => compactZeroCount κ (B n) W/(B n : ℂ)^3) =ᶠ[atTop]
      (fun n => majorArcIntegral κ n (B n) (n : ℝ) W/(B n : ℂ)^3+
        minorArcIntegral κ n (B n) W/(B n : ℂ)^3) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [←actual_major_plus_minor_count κ n (by omega) (B n) (hB n) (hscale n) W hW,add_div]
  exact (by simpa only [add_zero] using hmajor.add hminor).congr' he.symm

end ActualOriginalCircleMinorArcIdentity318
