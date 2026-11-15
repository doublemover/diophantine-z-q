module
public import ActualOriginalWeightedQuadraticShift318
public section
noncomputable section
namespace ActualOriginalLineCorrelation318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalFiniteAbel318 ActualOriginalPairedWeightVariation318
open ActualOriginalWeightedLinearCancellation318
open scoped BigOperators

/-- An actual integral line in the original five coordinates. Choosing
any coordinate unit vector supplies the corresponding literal box slice. -/
@[expose] def linePoint (y v : Coordinates ℤ) (j : ℕ) : Coordinates ℤ :=
  ((y.1.1+(j : ℤ)*v.1.1,y.1.2+(j : ℤ)*v.1.2),
    (y.2.1.1+(j : ℤ)*v.2.1.1,y.2.1.2+(j : ℤ)*v.2.1.2),
    y.2.2+(j : ℤ)*v.2.2)

lemma actual_bilinear_line (κ : ℤ) (h y v : Coordinates ℤ) (j : ℕ) :
    originalBilinear κ h (linePoint y v j)=
      originalBilinear κ h y+(j : ℤ)*originalBilinear κ h v := by
  unfold originalBilinear linePoint
  ring

lemma actual_original_line_phase (κ : ℤ) (h y v : Coordinates ℤ) (j : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (equation κ (h+linePoint y v j)) θ*
      starRingEnd ℂ (fourier (equation κ (linePoint y v j)) θ)=
    fourier (equation κ h+2*originalBilinear κ h y) θ*
      fourier ((2*originalBilinear κ h v)*(j : ℤ)) θ := by
  rw [←fourier_neg,←fourier_add,←fourier_add]
  congr 1
  have he := actual_original_polarization κ h (linePoint y v j)
  rw [actual_bilinear_line] at he
  linear_combination he

/-- The literal original weighted two-point correlation along a line.
Both values come from the SAME ambient weight w, at the actual endpoints. -/
@[expose] def originalLineCorrelation (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h y v : Coordinates ℤ) (N : ℕ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range N,
    (w (h+linePoint y v j)*starRingEnd ℂ (w (linePoint y v j)))*
    (fourier (equation κ (h+linePoint y v j)) θ*
      starRingEnd ℂ (fourier (equation κ (linePoint y v j)) θ))

lemma actual_original_line_correlation_linear (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h y v : Coordinates ℤ) (N : ℕ) (θ : AddCircle (1 : ℝ)) :
    originalLineCorrelation κ w h y v N θ=
      fourier (equation κ h+2*originalBilinear κ h y) θ*
        weightedLinearInterval (2*originalBilinear κ h v) 0
          (pairedWeight (fun j => w (h+linePoint y v j))
            (fun j => w (linePoint y v j))) N θ := by
  simp only [originalLineCorrelation,actual_original_line_phase,weightedLinearInterval,
    weightedPrefix,pairedWeight,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Actual weighted cancellation inside the original five-variable
correlation, valid for every integer direction. No weight separability.
Assembling all slices and minor-domain rational approximation remains open. -/
theorem actual_original_line_cancellation (κ : ℤ) (w : Coordinates ℤ → ℂ)
    (h y v : Coordinates ℤ) (N : ℕ) (θ : AddCircle (1 : ℝ))
    (hn : fourier (2*originalBilinear κ h v) θ≠1) :
    ‖originalLineCorrelation κ w h y v (N+1) θ‖≤
      min ((N : ℝ)+1) (2/‖fourier (2*originalBilinear κ h v) θ-1‖)*
        variation (pairedWeight (fun j => w (h+linePoint y v j))
          (fun j => w (linePoint y v j))) N := by
  rw [actual_original_line_correlation_linear,norm_mul]
  have he : ‖fourier (equation κ h+2*originalBilinear κ h y) θ‖=1 := Circle.norm_coe _
  rw [he,one_mul]
  exact actual_weighted_linear_cancellation _ 0 _ N θ hn

end ActualOriginalLineCorrelation318
