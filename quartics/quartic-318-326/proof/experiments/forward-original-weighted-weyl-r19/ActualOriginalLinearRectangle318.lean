module
public import ActualOriginalSmoothAxisRectangle318
public section
noncomputable section
namespace ActualOriginalLinearRectangle318
open QuadricCRTAssembly318 ActualOriginalQuadraticPolarization318
open ActualOriginalLineCorrelation318 ActualOriginalAxisRectangle318
open ActualOriginalTwoAxisCancellation318 ActualOriginalRationalBlockReciprocalSum318
open scoped BigOperators

@[expose] def originalFourierAxis (κ : ℤ) (h : Coordinates ℤ) (t : ℝ)
    (a : Coordinates ℤ × ℕ) : Axis (Coordinates ℤ) where
  step := a.1
  steps := a.2
  phase := fun j => fourier ((2*originalBilinear κ h a.1)*(j : ℤ)) (t : AddCircle (1 : ℝ))
  cap := fourierChordCap ((a.2 : ℝ)+1) (2*originalBilinear κ h a.1) t

/-- Literal original linearized phase, with the paired weight kept at
its true lattice point. Every axis has its full steps+1 terms. -/
@[expose] def originalLinearRectangle (κ : ℤ) (g : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) :
    List (Coordinates ℤ × ℕ) → Coordinates ℤ → ℂ
  | [], x => g x*fourier (2*originalBilinear κ h x) θ
  | a::as, x => ∑ j∈Finset.range (a.2+1), originalLinearRectangle κ g θ h as (x+j • a.1)

lemma actual_nsmul_line_point (x u : Coordinates ℤ) (j : ℕ) :
    x+j • u=linePoint x u j := by
  ext <;> simp [linePoint,nsmul_eq_mul]

lemma actual_original_linear_step (κ : ℤ) (h x u : Coordinates ℤ) (j : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (2*originalBilinear κ h (x+j • u)) θ=
      fourier (2*originalBilinear κ h x) θ*
        fourier ((2*originalBilinear κ h u)*(j : ℤ)) θ := by
  rw [actual_nsmul_line_point,←fourier_add]
  congr 1
  rw [actual_bilinear_line]
  ring

/-- ONLY the original phase is factored. g remains one arbitrary
multivariate function inside every nested sum. -/
theorem actual_original_linear_rectangle_factor (κ : ℤ) (g : Coordinates ℤ → ℂ)
    (t : ℝ) (h : Coordinates ℤ) (as : List (Coordinates ℤ × ℕ)) : ∀ x,
    originalLinearRectangle κ g (t : AddCircle (1 : ℝ)) h as x=
      fourier (2*originalBilinear κ h x) (t : AddCircle (1 : ℝ))*
        axisRectangle g (as.map (originalFourierAxis κ h t)) x := by
  induction as with
  | nil => intro x; simp only [originalLinearRectangle,List.map_nil,axisRectangle]; ring
  | cons a as ih =>
    intro x
    simp only [originalLinearRectangle,List.map_cons,axisRectangle,ih,
      originalFourierAxis,actual_original_linear_step,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma actual_original_fourier_axis_prefix (κ : ℤ) (h : Coordinates ℤ) (t : ℝ)
    (a : Coordinates ℤ × ℕ) :
    ∀ n≤(originalFourierAxis κ h t a).steps+1,
      ‖ActualOriginalFiniteAbel318.prefix (originalFourierAxis κ h t a).phase n‖≤
        (originalFourierAxis κ h t a).cap := by
  intro n hn
  simpa only [originalFourierAxis,Nat.cast_add,Nat.cast_one] using
    actual_fourier_prefix_cap (2*originalBilinear κ h a.1) t (a.2+1) n hn

end ActualOriginalLinearRectangle318
