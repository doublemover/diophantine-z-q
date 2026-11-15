module
public import ActualOriginalPositiveCountLowerBound318
public section
noncomputable section
namespace ActualOriginalQuantitativePrimitiveCount318
open QuadricCRTAssembly318 ActualOriginalBoundedPrimitiveBox318 ActualOriginalBoundedPrimitiveMass318
open ActualOriginalPositiveCountLowerBound318 ActualOriginalPositiveCountAsymptotic318
open ActualOriginalCompactCircleCount318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleMinorDecay318 Filter
open ActualOriginalRealGoodRegion318
open scoped Topology ContDiff

/-- An actual positive B³ count forces at least c B² globally primitive
points inside the actual canonical radius-O(B) box. All constants and the
fixed scale parameter are produced from the SAME original weight. This
is a lower bound, not a primitive B³ asymptotic or prime-value result. -/
theorem actual_primitive_quadratic_lower_of_positive_count {J : Type*} [Fintype J]
    (κ : ℕ) (γ : J → ℝ) (S : ℝ) (hS : 0<S) (h : PositiveFullCountInput κ γ S) :
    ∃ p : ℕ, ∃ R c : ℝ, 1≤R ∧ 0<c ∧
      ∀ᶠ n in atTop, c*(flexibleScale p (n+2))^2≤
        ((primitiveBox (κ : ℤ) γ
          (canonicalMomentRadius R (flexibleScale p (n+2)))).card : ℝ) := by
  obtain ⟨x,W,η,p,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hBt,hcount⟩ := h
  have hregion : ∀ y∈tsupport W,y∈region γ := fun y hy => (hsupport y hy).1
  obtain ⟨R,A,hR,hA,hbound⟩ := actual_bounded_primitive_linear_mass (κ : ℤ) γ W
    hW.continuous hWc hregion
  have hB : ∀ n : ℕ,1≤flexibleScale p (n+2) := fun n =>
    (actual_flexible_minor_scale p (n+2) (by omega)).2.1
  have hBp : ∀ n : ℕ,0<flexibleScale p (n+2) := fun n => by linarith [hB n]
  have hlow := actual_positive_count_norm_lower
    (fun n => compactZeroCount (κ : ℤ) (flexibleScale p (n+2)) W)
    (fun n => flexibleScale p (n+2)) hBp S hS hcount
  let c := S/(2*A)
  refine ⟨p,R,c,hR,div_pos hS (mul_pos (by norm_num) hA),?_⟩
  filter_upwards [hlow] with n hn
  let B := flexibleScale p (n+2)
  let P : ℝ := (primitiveBox (κ : ℤ) γ (canonicalMomentRadius R B)).card
  have hh : (S/2)*B^3≤P*A*B := hn.trans (hbound B (hB n))
  have hh' : ((S/2)*B^2)*B≤(P*A)*B := by nlinarith only [hh]
  have hquot : (S/2)*B^2≤P*A := (mul_le_mul_right (hBp n)).mp hh'
  calc
    c*B^2 = ((S/2)*B^2)/A := by dsimp [c]; field_simp [ne_of_gt hA] <;> ring
    _ ≤ P := (div_le_iff₀ hA).mpr hquot

theorem actual318_primitive_quadratic_lower {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ p : ℕ, ∃ R c : ℝ, 1≤R ∧ 0<c ∧
      ∀ᶠ n in atTop, c*(flexibleScale p (n+2))^2≤
        ((primitiveBox 318 γ (canonicalMomentRadius R (flexibleScale p (n+2)))).card : ℝ) := by
  obtain ⟨S,hS,hprod,h⟩ := actual318_positive_full_count γ
  exact actual_primitive_quadratic_lower_of_positive_count 318 γ S hS h

theorem actual326_primitive_quadratic_lower {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ p : ℕ, ∃ R c : ℝ, 1≤R ∧ 0<c ∧
      ∀ᶠ n in atTop, c*(flexibleScale p (n+2))^2≤
        ((primitiveBox 326 γ (canonicalMomentRadius R (flexibleScale p (n+2)))).card : ℝ) := by
  obtain ⟨S,hS,hprod,h⟩ := actual326_positive_full_count γ
  exact actual_primitive_quadratic_lower_of_positive_count 326 γ S hS h
end ActualOriginalQuantitativePrimitiveCount318
