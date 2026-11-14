module
public import ActualOriginalUniformPairedVariation318
public section
noncomputable section
namespace ActualOriginalCorrelationBasePoints318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalWeightedWeylIdentity318
open scoped BigOperators

@[expose] def basePoints (s : Finset (Coordinates ℤ)) (h : Coordinates ℤ) :
    Finset (Coordinates ℤ) := by
  classical
  exact s.filter (fun y => h+y∈s)

/-- Exact enumeration of EVERY ordered pair in the original displacement
fiber by its actual second endpoint. No square-root or modular substitute. -/
theorem actual_correlation_base_points (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) :
    linearCorrelation κ s w θ h=
      ∑ y ∈ basePoints s h, w (h+y)*starRingEnd ℂ (w y)*
        fourier (2*originalBilinear κ h y) θ := by
  classical
  symm
  unfold basePoints linearCorrelation
  apply Finset.sum_bij (fun y _ => (h+y,y))
  · intro y hy
    have hh := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hh.2,hh.1⟩,by simp⟩
  · intro y hy z hz he
    exact congrArg Prod.snd he
  · intro xy hxy
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    have he : h+xy.2=xy.1 := by rw [←hd]; abel
    refine ⟨xy.2,Finset.mem_filter.mpr ⟨hy,by rwa [he]⟩,?_⟩
    exact Prod.ext he rfl
  · intro y hy
    rfl

end ActualOriginalCorrelationBasePoints318
