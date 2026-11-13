module
public import ActualOriginalTwoAxisSliceIdentity318
public section
noncomputable section
namespace ActualOriginalTwoAxisCancellation318
open QuadricCRTAssembly318 ActualOriginalFiniteAbel318
open ActualOriginalLinearIntervalCancellation318 ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalMixedAbelIdentity318 ActualOriginalMixedAbelBound318
open ActualOriginalTwoAxisSliceIdentity318

lemma actual_fourier_prefix_cap (c : ℤ) (t : ℝ) (N n : ℕ) (hn : n≤N) :
    ‖prefix (fun j => fourier (c*(j : ℤ)) (t : AddCircle (1 : ℝ))) n‖≤
      fourierChordCap (N : ℝ) c t := by
  by_cases h : fourier c (t : AddCircle (1 : ℝ))=1
  · rw [fourierChordCap,if_pos h]
    have hb := actual_linear_interval_length_bound c 0 n (t : AddCircle (1 : ℝ))
    have hb' : ‖prefix (fun j => fourier (c*(j : ℤ)) (t : AddCircle (1 : ℝ))) n‖≤(n : ℝ) := by
      simpa only [linearIntervalSum,prefix,zero_add] using hb
    apply hb'.trans
    exact_mod_cast hn
  · rw [fourierChordCap,if_neg h]
    have hb := actual_linear_interval_cancellation c 0 n (t : AddCircle (1 : ℝ)) h
    have hb' : ‖prefix (fun j => fourier (c*(j : ℤ)) (t : AddCircle (1 : ℝ))) n‖≤
        min (n : ℝ) (2/‖fourier c (t : AddCircle (1 : ℝ))-1‖) := by
      simpa only [linearIntervalSum,prefix,zero_add] using hb
    apply hb'.trans
    exact min_le_min (by exact_mod_cast hn) le_rfl

/-- TWO actual original directions cancel multiplicatively, including
resonances via full-length kernels. The cost is the genuine mixed variation
of BOTH original endpoint weights, not an assumed separable factorization. -/
theorem actual_original_two_axis_cancellation (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (t : ℝ) (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (N M : ℕ) :
    ‖originalPlaneCorrelation κ w (t : AddCircle (1 : ℝ)) h lo₀ lo₁ c d e (N+1) (M+1)‖≤
      fourierChordCap ((N : ℝ)+1) (2*h.1.1) t*
        fourierChordCap ((M : ℝ)+1) (2*h.1.2) t*
          mixedVariation (planePairedWeight w h lo₀ lo₁ c d e) N M := by
  rw [actual_original_plane_factor,norm_mul]
  have hu : ‖fourier (2*ActualOriginalQuadraticPolarization318.originalBilinear κ h
      (planePoint lo₀ lo₁ c d e 0 0)) (t : AddCircle (1 : ℝ))‖=1 := Circle.norm_coe _
  rw [hu,one_mul]
  apply actual_rectangular_abel_bound
  · intro n hn
    simpa only [Nat.cast_add,Nat.cast_one] using actual_fourier_prefix_cap (2*h.1.1) t (N+1) n hn
  · intro m hm
    simpa only [Nat.cast_add,Nat.cast_one] using actual_fourier_prefix_cap (2*h.1.2) t (M+1) m hm

lemma actual_original_plane_empty_left (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (M : ℕ) :
    originalPlaneCorrelation κ w θ h lo₀ lo₁ c d e 0 M=0 := by
  simp [originalPlaneCorrelation]

lemma actual_original_plane_empty_right (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (lo₀ lo₁ c d e : ℤ) (N : ℕ) :
    originalPlaneCorrelation κ w θ h lo₀ lo₁ c d e N 0=0 := by
  simp [originalPlaneCorrelation]

end ActualOriginalTwoAxisCancellation318
