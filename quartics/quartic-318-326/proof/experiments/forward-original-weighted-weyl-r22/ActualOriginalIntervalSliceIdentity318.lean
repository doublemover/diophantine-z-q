module
public import ActualOriginalUniformLineCancellation318
public section
noncomputable section
namespace ActualOriginalIntervalSliceIdentity318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalLineCorrelation318 ActualOriginalBoxSliceAggregation318
open ActualOriginalBoxOverlap318
open scoped BigOperators

@[expose] def firstDirection : Coordinates ℤ := ((1,0),(0,0),0)

lemma actual_first_line (lo b c d e : ℤ) (j : ℕ) :
    linePoint ((lo,b),(c,d),e) firstDirection j=((lo+(j : ℤ),b),(c,d),e) := by
  simp [linePoint,firstDirection]

lemma actual_full_line_phase (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h y v : Coordinates ℤ) (N : ℕ) (θ : AddCircle (1 : ℝ)) :
    originalLineCorrelation κ w h y v N θ=fourier (equation κ h) θ*
      ∑ j ∈ Finset.range N, w (h+linePoint y v j)*starRingEnd ℂ (w (linePoint y v j))*
        fourier (2*originalBilinear κ h (linePoint y v j)) θ := by
  unfold originalLineCorrelation
  simp_rw [actual_original_phase_difference,add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The interval slices in the exact box decomposition are the SAME
original line correlations controlled by the uniform smooth-weight bound,
up to the displayed unit phase. Empty overlaps are also included. -/
theorem actual_interval_slice_identity (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h : Coordinates ℤ) (lo hi b c d e : ℤ) (θ : AddCircle (1 : ℝ)) :
    originalLineCorrelation κ w h ((lo,b),(c,d),e) firstDirection (hi-lo+1).toNat θ=
      fourier (equation κ h) θ*sliceCorrelation κ w θ h (Finset.Icc lo hi) b c d e := by
  rw [actual_full_line_phase]
  unfold sliceCorrelation
  rw [actual_integer_interval_sum]
  simp only [actual_first_line]

lemma actual_interval_slice_norm (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h : Coordinates ℤ) (lo hi b c d e : ℤ) (θ : AddCircle (1 : ℝ)) :
    ‖sliceCorrelation κ w θ h (Finset.Icc lo hi) b c d e‖=
      ‖originalLineCorrelation κ w h ((lo,b),(c,d),e) firstDirection (hi-lo+1).toNat θ‖ := by
  rw [actual_interval_slice_identity,norm_mul]
  have hh : ‖fourier (equation κ h) θ‖=1 := Circle.norm_coe _
  rw [hh,one_mul]

end ActualOriginalIntervalSliceIdentity318
