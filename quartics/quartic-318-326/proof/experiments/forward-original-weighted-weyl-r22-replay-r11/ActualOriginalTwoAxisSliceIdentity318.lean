module
public import ActualOriginalMixedVariationBudget318
public section
noncomputable section
namespace ActualOriginalTwoAxisSliceIdentity318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalBoxSliceAggregation318 ActualOriginalBoxOverlap318
open ActualOriginalMixedAbelIdentity318
open scoped BigOperators

@[expose] def planePoint (lo₀ lo₁ c d e : ℤ) (i j : ℕ) : Coordinates ℤ :=
  ((lo₀+(i : ℤ),lo₁+(j : ℤ)),(c,d),e)
@[expose] def planePairedWeight (w : Coordinates ℤ → ℂ) (h : Coordinates ℤ)
    (lo₀ lo₁ c d e : ℤ) (i j : ℕ) : ℂ :=
  w (h+planePoint lo₀ lo₁ c d e i j)*starRingEnd ℂ (w (planePoint lo₀ lo₁ c d e i j))
@[expose] def originalPlaneCorrelation (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (N M : ℕ) : ℂ :=
  ∑ i∈Finset.range N, ∑ j∈Finset.range M,
    planePairedWeight w h lo₀ lo₁ c d e i j*
      fourier (2*originalBilinear κ h (planePoint lo₀ lo₁ c d e i j)) θ

/-- Exact identification with the SAME first-axis slices used by the
original five-variable box decomposition, now summed over the second axis.
All interval endpoints and empty intervals are included. -/
theorem actual_original_two_axis_slice_identity (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (lo₀ hi₀ lo₁ hi₁ c d e : ℤ) :
    (∑ b∈Finset.Icc lo₁ hi₁, sliceCorrelation κ w θ h (Finset.Icc lo₀ hi₀) b c d e)=
      originalPlaneCorrelation κ w θ h lo₀ lo₁ c d e
        (hi₀-lo₀+1).toNat (hi₁-lo₁+1).toNat := by
  unfold sliceCorrelation
  rw [actual_integer_interval_sum]
  simp_rw [actual_integer_interval_sum]
  rw [Finset.sum_comm]
  rfl

lemma actual_original_plane_phase (κ : ℤ) (θ : AddCircle (1 : ℝ))
    (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (i j : ℕ) :
    fourier (2*originalBilinear κ h (planePoint lo₀ lo₁ c d e i j)) θ=
      fourier (2*originalBilinear κ h (planePoint lo₀ lo₁ c d e 0 0)) θ*
        fourier ((2*h.1.1)*(i : ℤ)) θ*fourier ((2*h.1.2)*(j : ℤ)) θ := by
  simp only [←fourier_add]
  congr 1
  unfold originalBilinear planePoint
  simp only [Nat.cast_zero,add_zero]
  ring

/-- Only the PHASE factors. The actual two-variable paired weight is
retained intact and is controlled by mixed Abel variation downstream. -/
theorem actual_original_plane_factor (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (N M : ℕ) :
    originalPlaneCorrelation κ w θ h lo₀ lo₁ c d e N M=
      fourier (2*originalBilinear κ h (planePoint lo₀ lo₁ c d e 0 0)) θ*
        rectangularWeighted
          (fun i => fourier ((2*h.1.1)*(i : ℤ)) θ)
          (fun j => fourier ((2*h.1.2)*(j : ℤ)) θ)
          (planePairedWeight w h lo₀ lo₁ c d e) N M := by
  simp only [originalPlaneCorrelation,rectangularWeighted,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_original_plane_phase]
  ring

end ActualOriginalTwoAxisSliceIdentity318
