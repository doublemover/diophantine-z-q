module
public import ActualOriginalCommonScaleMajorError318
public section
noncomputable section
namespace ActualOriginalCommonScaleCountLimit318
open QuadricCRTAssembly318 ActualOriginalPolynomialMinorScale318
open ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleMinorDecay318 ActualOriginalCommonScaleMajorError318
open ActualOriginalFiniteMajorArcError318 ActualOriginalMajorArcIntegral318
open ActualOriginalCircleMinorArcIdentity318 ActualOriginalCompactCircleCount318
open ActualOriginalZeroModeLimit318 Filter MeasureTheory
open scoped ContDiff Topology

/-- A single actual scale simultaneously consumes the zero mode,
produced major remainder and produced complementary minor integral.
The zero-mode limit is the sole analytic main-term input left here. -/
theorem actual_common_scale_count_limit (κ : ℕ) (hκ : 0<κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hi : Integrable (originalOscillation (κ : ℝ) W)) (S : ℂ)
    (hz : Tendsto (fun n : ℕ => normalizedZeroMode (κ : ℤ) W
      (minorCutoff (n+2)+1) (minorCutoff (n+2) : ℝ)) atTop (𝓝 S)) :
    ∃ p : ℕ,
      Tendsto (fun n : ℕ => majorArcIntegral (κ : ℤ) (minorCutoff (n+2))
        (flexibleScale p (n+2)) (minorCutoff (n+2) : ℝ) W/(flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 S) ∧
      Tendsto (fun n : ℕ => minorArcIntegral (κ : ℤ) (minorCutoff (n+2))
        (flexibleScale p (n+2)) W/(flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => compactZeroCount (κ : ℤ) (flexibleScale p (n+2)) W/
        (flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 S) := by
  obtain ⟨p,he⟩ := actual_common_scale_major_error_limit κ hκ W hW hc
  have hB (n : ℕ) : 0<flexibleScale p (n+2) :=
    lt_of_lt_of_le (by norm_num) (actual_flexible_minor_scale p (n+2) (by omega)).2.1
  have hmajor : Tendsto (fun n : ℕ => majorArcIntegral (κ : ℤ) (minorCutoff (n+2))
      (flexibleScale p (n+2)) (minorCutoff (n+2) : ℝ) W/(flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 S) := by
    have hid (n : ℕ) : majorArcIntegral (κ : ℤ) (minorCutoff (n+2))
        (flexibleScale p (n+2)) (minorCutoff (n+2) : ℝ) W/(flexibleScale p (n+2) : ℂ)^3=
        normalizedZeroMode (κ : ℤ) W (minorCutoff (n+2)+1) (minorCutoff (n+2) : ℝ)+
        finiteMajorArcError κ (minorCutoff (n+2)) (flexibleScale p (n+2))
          (minorCutoff (n+2) : ℝ) W/(flexibleScale p (n+2) : ℂ)^3 := by
      rw [actual_major_arc_decomposition κ _ _ _ (ne_of_gt (hB n)) W hc hi]
      have hnz : (flexibleScale p (n+2) : ℂ)≠0 := by exact_mod_cast (ne_of_gt (hB n))
      field_simp [hnz]
    simp_rw [hid]
    simpa only [add_zero] using hz.add he
  have hminor := actual_flexible_minor_decay p (κ : ℤ) (by exact_mod_cast (Nat.ne_of_gt hκ)) W hW hc
  refine ⟨p,hmajor,hminor,?_⟩
  have hid (n : ℕ) : compactZeroCount (κ : ℤ) (flexibleScale p (n+2)) W/(flexibleScale p (n+2) : ℂ)^3=
      majorArcIntegral (κ : ℤ) (minorCutoff (n+2)) (flexibleScale p (n+2))
        (minorCutoff (n+2) : ℝ) W/(flexibleScale p (n+2) : ℂ)^3+
      minorArcIntegral (κ : ℤ) (minorCutoff (n+2)) (flexibleScale p (n+2)) W/(flexibleScale p (n+2) : ℂ)^3 := by
    obtain ⟨hN,hB1,hs⟩ := actual_flexible_minor_scale p (n+2) (by omega)
    rw [←actual_major_plus_minor_count (κ : ℤ) (minorCutoff (n+2)) hN
      (flexibleScale p (n+2)) (hB n) hs W hc,add_div]
  simp_rw [hid]
  simpa only [add_zero] using hmajor.add hminor

end ActualOriginalCommonScaleCountLimit318
