module
public import ActualOriginalCommonScaleCountLimit318
public section
noncomputable section
namespace ActualOriginalPositiveCountAsymptotic318
open QuadricCRTAssembly318 ActualOriginalCommonScaleCountLimit318
open ActualOriginalPolynomialMinorScale318 ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleMinorDecay318
open ActualOriginalZeroModeLimit318 ActualOriginalAllPrimeFactors318 ActualOriginalCompactCircleCount318
open ActualOriginalPositiveSingularIntegral318 ActualOriginalRealGoodRegion318 ActualOriginalPositiveGraphIntegral318
open Filter MeasureTheory
open scoped ContDiff Topology

/-- Actual positive full weighted integer-zero asymptotic on the original
quadric, retaining the original prime-form REGION only. This is not a
prime-value or primitive-point sieve conclusion. -/
@[expose] def PositiveFullCountInput {J : Type*} [Fintype J]
    (κ : ℕ) (γ : J → ℝ) (S : ℝ) : Prop :=
  ∃ (x : Coordinates ℝ) (W : Coordinates ℝ → ℝ) (η : ℝ) (p : ℕ),
    equation (κ : ℝ) x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
    ContDiff ℝ ∞ W ∧ (∀ y,0≤W y) ∧ 0<W x ∧
    (∀ y∈tsupport W,y∈region γ ∧ η<ActualQuadricTaylor318.gradient (κ : ℝ) y 0) ∧
    graphMass (κ : ℝ) W=1 ∧
    Tendsto (fun n : ℕ => flexibleScale p (n+2)) atTop atTop ∧
    Tendsto (fun n : ℕ => compactZeroCount (κ : ℤ) (flexibleScale p (n+2)) W/
      (flexibleScale p (n+2) : ℂ)^3) atTop (𝓝 (S : ℂ))

lemma actual_positive_count_of_zero_mode {J : Type*} [Fintype J]
    (κ : ℕ) (hκ : 0<κ) (γ : J → ℝ) (S : ℝ)
    (h : NormalizedZeroModeInput (κ : ℤ) γ S) : PositiveFullCountInput κ γ S := by
  obtain ⟨x,W,η,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hi,hlim⟩ := h
  simp only [Int.cast_natCast] at hx hsupport hmass hi
  have hN : Tendsto (fun n : ℕ => minorCutoff (n+2)) atTop atTop :=
    (actual_flexible_scale_properties 0).1
  have hN1 : Tendsto (fun n : ℕ => minorCutoff (n+2)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right _ 1) hN
  have hNR : Tendsto (fun n : ℕ => (minorCutoff (n+2) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hz := hlim (fun n => minorCutoff (n+2)+1) (fun n => (minorCutoff (n+2) : ℝ)) hN1 hNR
  obtain ⟨p,hmajor,hminor,hcount⟩ := actual_common_scale_count_limit κ hκ W hW hWc hi (S : ℂ) hz
  exact ⟨x,W,η,p,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,
    (actual_flexible_scale_properties p).2.1,hcount⟩

theorem actual318_positive_full_count {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0<S ∧ HasProd density318 S ∧ PositiveFullCountInput 318 γ S := by
  obtain ⟨S,hS,hprod,h⟩ := actual318_positive_zero_mode_input γ
  exact ⟨S,hS,hprod,actual_positive_count_of_zero_mode 318 (by norm_num) γ S h⟩

theorem actual326_positive_full_count {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0<S ∧ HasProd density326 S ∧ PositiveFullCountInput 326 γ S := by
  obtain ⟨S,hS,hprod,h⟩ := actual326_positive_zero_mode_input γ
  exact ⟨S,hS,hprod,actual_positive_count_of_zero_mode 326 (by norm_num) γ S h⟩

end ActualOriginalPositiveCountAsymptotic318
