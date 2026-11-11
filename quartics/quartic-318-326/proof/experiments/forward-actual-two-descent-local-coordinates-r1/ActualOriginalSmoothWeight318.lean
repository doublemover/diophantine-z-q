module
public import ActualOriginalRealGoodRegion318
public section
noncomputable section
namespace ActualOriginalSmoothWeight318
open QuadricCRTAssembly318 ActualOriginalPositiveRealPoint318 ActualOriginalRealGoodRegion318
open scoped Topology ContDiff
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J]

/-- A genuine compactly supported smooth ambient weight on the original
five-dimensional source. No measure or singular-integral identity is assumed. -/
theorem actual_original_smooth_weight (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<η ∧ HasCompactSupport W ∧ ContDiff ℝ ∞ W ∧
      (∀y,0≤W y ∧ W y≤1) ∧ W x=1 ∧
      (∀y∈tsupport W, y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) := by
  obtain ⟨x,hQ,ha,hc,hw,hf,hgrad⟩ := actual_positive_real_point κ hκ γ
  have hx : x∈region γ := ⟨ha,hc,hw,hf⟩
  obtain ⟨W,hWs,hWc,hWd,hWr,hWx⟩ :=
    exists_contDiff_tsupport_subset (n:=∞)
      ((protectedRegion_open γ x).mem_nhds (self_mem_protected γ x hx))
  refine ⟨x,W,x.1.1,hQ,ha,hWc,hWd,?_,hWx,?_⟩
  · intro y
    exact hWr ⟨y,rfl⟩
  · intro y hy
    have h := hWs hy
    exact ⟨h.1,actual_gradient_lower κ γ x y h⟩

end ActualOriginalSmoothWeight318
