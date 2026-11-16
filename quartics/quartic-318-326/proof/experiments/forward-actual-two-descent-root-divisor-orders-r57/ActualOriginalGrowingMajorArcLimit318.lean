module
public import ActualOriginalArcDiagonal318
public section
noncomputable section
namespace ActualOriginalGrowingMajorArcLimit318
open QuadricCRTAssembly318 ActualOriginalMajorArcIntegral318 ActualOriginalArcDiagonal318
open ActualOriginalZeroModeLimit318 ActualOriginalFiniteMajorArcError318
open ActualOriginalPositiveSingularIntegral318 ActualOriginalRealGoodRegion318
open ActualOriginalPositiveGraphIntegral318 ActualOriginalAllPrimeFactors318
open Filter MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

lemma denominator_cutoff_tendsto : Tendsto (fun n : ℕ => n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_add_right n 1) tendsto_id

/-- A genuine simultaneous major-arc limit for the original exponential
sum. BOTH the denominator bound and the Fourier cutoff grow, and the actual
nonzero-mode error is produced by the existing full Poisson estimates. -/
theorem actual_growing_major_arc_limit (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hi : Integrable (originalOscillation (κ : ℝ) W)) (S : ℂ)
    (hz : Tendsto (fun n : ℕ => normalizedZeroMode (κ : ℤ) W (n+1) (n : ℝ))
      atTop (𝓝 S)) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧ Tendsto B atTop atTop ∧
      (∀ n, ((n : ℝ)+1)^3 ≤ B n) ∧
      Tendsto (fun n => majorArcIntegral (κ : ℤ) n (B n) (n : ℝ) W / (B n : ℂ)^3)
        atTop (𝓝 S) := by
  obtain ⟨B,hB,hBt,hBc,heBound,he⟩ := actual_growing_arc_error κ hκ W hW hWc
  refine ⟨B,hB,hBt,hBc,?_⟩
  have heq (n : ℕ) :
      majorArcIntegral (κ : ℤ) n (B n) (n : ℝ) W / (B n : ℂ)^3 =
        normalizedZeroMode (κ : ℤ) W (n+1) (n : ℝ) +
          finiteMajorArcError κ n (B n) (n : ℝ) W / (B n : ℂ)^3 := by
    rw [actual_major_arc_decomposition κ n (B n) (n : ℝ) (hB n).ne' W hWc hi]
    have hn : (B n : ℂ) ≠ 0 := by exact_mod_cast (hB n).ne'
    field_simp [hn]
  simp_rw [heq]
  simpa only [add_zero] using hz.add he

/-- The same original support, positivity, and normalized graph mass are
kept in the growing-arc result. This is an indexed arc integral theorem;
there is no assertion here about the complementary minor-arc integral. -/
@[expose] def GrowingMajorArcInput {J : Type*} [Fintype J]
    (κ : ℕ) (γ : J → ℝ) (S : ℝ) : Prop :=
  ∃ (x : Coordinates ℝ) (W : Coordinates ℝ → ℝ) (η : ℝ) (B : ℕ → ℝ),
    equation (κ : ℝ) x = 0 ∧ 0 < x.1.1 ∧ 0 < η ∧ HasCompactSupport W ∧
    ContDiff ℝ ∞ W ∧ (∀ y, 0 ≤ W y) ∧ 0 < W x ∧
    (∀ y ∈ tsupport W, y ∈ region γ ∧ η < ActualQuadricTaylor318.gradient (κ : ℝ) y 0) ∧
    graphMass (κ : ℝ) W = 1 ∧ Integrable (originalOscillation (κ : ℝ) W) ∧
    (∀ n, 0 < B n) ∧ Tendsto B atTop atTop ∧ (∀ n, ((n : ℝ)+1)^3 ≤ B n) ∧
    Tendsto (fun n => majorArcIntegral (κ : ℤ) n (B n) (n : ℝ) W / (B n : ℂ)^3)
      atTop (𝓝 (S : ℂ))

theorem actual_input_of_zero_mode {J : Type*} [Fintype J]
    (κ : ℕ) (hκ : 0 < κ) (γ : J → ℝ) (S : ℝ)
    (h : NormalizedZeroModeInput (κ : ℤ) γ S) : GrowingMajorArcInput κ γ S := by
  obtain ⟨x,W,η,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hi,hlim⟩ := h
  simp only [Int.cast_natCast] at hx hsupport hmass hi
  have hz := hlim (fun n => n+1) (fun n : ℕ => (n : ℝ))
    denominator_cutoff_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨B,hB,hBt,hBc,hM⟩ := actual_growing_major_arc_limit κ hκ W hW hWc hi (S : ℂ) hz
  exact ⟨x,W,η,B,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hi,hB,hBt,hBc,hM⟩

theorem actual318_positive_growing_major_arcs {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0 < S ∧ HasProd density318 S ∧ GrowingMajorArcInput 318 γ S := by
  obtain ⟨S,hS,hprod,h⟩ := actual318_positive_zero_mode_input γ
  exact ⟨S,hS,hprod,actual_input_of_zero_mode 318 (by norm_num) γ S h⟩

theorem actual326_positive_growing_major_arcs {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0 < S ∧ HasProd density326 S ∧ GrowingMajorArcInput 326 γ S := by
  obtain ⟨S,hS,hprod,h⟩ := actual326_positive_zero_mode_input γ
  exact ⟨S,hS,hprod,actual_input_of_zero_mode 326 (by norm_num) γ S h⟩

end ActualOriginalGrowingMajorArcLimit318
