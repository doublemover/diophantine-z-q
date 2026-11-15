module
public import ActualOriginalBoxOverlap318
public section
noncomputable section
namespace ActualOriginalBoxSliceAggregation318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCorrelationBasePoints318
open ActualOriginalFiniteBoxProduct318 ActualOriginalBoxOverlap318
open scoped BigOperators

@[expose] def sliceCorrelation (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (s₀ : Finset ℤ)
    (b c d e : ℤ) : ℂ :=
  ∑ a ∈ s₀, w (h+((a,b),(c,d),e))*starRingEnd ℂ (w ((a,b),(c,d),e))*
    fourier (2*originalBilinear κ h ((a,b),(c,d),e)) θ

/-- Exact slice aggregation of the ORIGINAL weighted displacement
fiber. All five overlap sets are constructed. Arbitrary w is preserved,
and no factorization of w is claimed. -/
theorem actual_box_correlation_slices (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (s₀ s₁ s₂ s₃ s₄ : Finset ℤ) :
    linearCorrelation κ (originalBox s₀ s₁ s₂ s₃ s₄) w θ h=
      ∑ b ∈ overlap s₁ h.1.2, ∑ c ∈ overlap s₂ h.2.1.1,
      ∑ d ∈ overlap s₃ h.2.1.2, ∑ e ∈ overlap s₄ h.2.2,
        sliceCorrelation κ w θ h (overlap s₀ h.1.1) b c d e := by
  rw [actual_correlation_base_points,actual_box_base_points]
  simp only [originalBox,Finset.sum_product,sliceCorrelation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]

/-- Triangle inequality over precisely the constructed complete slice
index set. This does not yet give the power-saving estimate for that sum. -/
theorem actual_box_correlation_slice_bound (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (s₀ s₁ s₂ s₃ s₄ : Finset ℤ) :
    ‖linearCorrelation κ (originalBox s₀ s₁ s₂ s₃ s₄) w θ h‖≤
      ∑ b ∈ overlap s₁ h.1.2, ∑ c ∈ overlap s₂ h.2.1.1,
      ∑ d ∈ overlap s₃ h.2.1.2, ∑ e ∈ overlap s₄ h.2.2,
        ‖sliceCorrelation κ w θ h (overlap s₀ h.1.1) b c d e‖ := by
  rw [actual_box_correlation_slices]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  exact norm_sum_le _ _

end ActualOriginalBoxSliceAggregation318
