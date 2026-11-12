module
public import ActualOriginalFinitePrimitiveMass318
public section
noncomputable section
namespace ActualOriginalPrimitiveInfinitude318
open QuadricCRTAssembly318 ActualOriginalPrimitiveRegionRays318 ActualOriginalFinitePrimitiveMass318
open ActualOriginalPositiveCountAsymptotic318 ActualOriginalCompactCircleCount318
open ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleMinorDecay318
open ActualOriginalRealGoodRegion318 Filter
open scoped Topology ContDiff

lemma actual_finite_primitive_normalized_zero {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (hfinite : (goodPrimitivePoints κ γ).Finite)
    (W : Coordinates ℝ → ℝ) (hW : Continuous W) (hc : HasCompactSupport W)
    (hregion : ∀ y∈tsupport W,y∈region γ) (B : ℕ → ℝ)
    (hB : ∀ n,1≤B n) (hBt : Tendsto B atTop atTop) :
    Tendsto (fun n => compactZeroCount κ (B n) W/(B n : ℂ)^3) atTop (𝓝 0) := by
  obtain ⟨A,hA,hbound⟩ := actual_finite_primitive_linear_mass κ γ hfinite W hW hc hregion
  have hmajor (n : ℕ) : ‖compactZeroCount κ (B n) W/(B n : ℂ)^3‖≤A/(B n)^2 := by
    have hpos : 0<B n := lt_of_lt_of_le (by norm_num) (hB n)
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
    apply (div_le_div_of_nonneg_right (hbound (B n) (hB n)) (pow_nonneg hpos.le 3)).trans_eq
    field_simp [ne_of_gt hpos]
    <;> ring
  have hi := tendsto_inv_atTop_zero.comp hBt
  have hh := (hi.pow 2).const_mul A
  have hlim : Tendsto (fun n => A/(B n)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero] using hh
  exact squeeze_zero_norm hmajor hlim

/-- Positive B³ asymptotics cannot be carried by finitely many primitive
rays, whose entire actual weighted mass is only O(B). Hence infinitely
many TRUE all-prime primitive original integer points exist in the region. -/
theorem actual_primitive_infinite_of_positive_count {J : Type*} [Fintype J]
    (κ : ℕ) (γ : J → ℝ) (S : ℝ) (hS : 0<S) (h : PositiveFullCountInput κ γ S) :
    (goodPrimitivePoints (κ : ℤ) γ).Infinite := by
  obtain ⟨x,W,η,p,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hBt,hcount⟩ := h
  intro hfinite
  have hregion : ∀ y∈tsupport W,y∈region γ := fun y hy => (hsupport y hy).1
  have hB : ∀ n : ℕ,1≤flexibleScale p (n+2) := fun n =>
    (actual_flexible_minor_scale p (n+2) (by omega)).2.1
  have hzero := actual_finite_primitive_normalized_zero (κ : ℤ) γ hfinite W hW.continuous hWc
    hregion (fun n => flexibleScale p (n+2)) hB hBt
  have he : (S : ℂ)=0 := tendsto_nhds_unique hcount hzero
  have heR : S=0 := Complex.ofReal_eq_zero.mp he
  linarith

theorem actual318_primitive_infinitely_many {J : Type*} [Fintype J] (γ : J → ℝ) :
    (goodPrimitivePoints 318 γ).Infinite := by
  obtain ⟨S,hS,hprod,h⟩ := actual318_positive_full_count γ
  exact actual_primitive_infinite_of_positive_count 318 γ S hS h

theorem actual326_primitive_infinitely_many {J : Type*} [Fintype J] (γ : J → ℝ) :
    (goodPrimitivePoints 326 γ).Infinite := by
  obtain ⟨S,hS,hprod,h⟩ := actual326_positive_full_count γ
  exact actual_primitive_infinite_of_positive_count 326 γ S hS h

end ActualOriginalPrimitiveInfinitude318
