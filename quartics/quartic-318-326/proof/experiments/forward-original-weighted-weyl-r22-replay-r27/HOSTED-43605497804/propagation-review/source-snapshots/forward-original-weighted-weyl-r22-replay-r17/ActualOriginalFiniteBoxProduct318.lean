module
public import ActualOriginalWeightedWeylBound318
public section
noncomputable section
namespace ActualOriginalFiniteBoxProduct318
open QuadricCRTAssembly318 ActualOriginalFiniteCircleIdentity318
open scoped BigOperators

@[expose] def quadraticIntervalSum (c : ℤ) (s : Finset ℤ)
    (θ : AddCircle (1 : ℝ)) : ℂ := ∑ x ∈ s, fourier (c*x^2) θ

@[expose] def originalBox (s₀ s₁ s₂ s₃ s₄ : Finset ℤ) : Finset (Coordinates ℤ) :=
  (s₀.product s₁).product ((s₂.product s₃).product s₄)

lemma actual_original_phase_product (κ : ℤ) (x : Coordinates ℤ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (equation κ x) θ =
      (fourier (1*x.1.1^2) θ*fourier (1*x.1.2^2) θ)*
      ((fourier ((-1)*x.2.1.1^2) θ*fourier ((-1)*x.2.1.2^2) θ)*
        fourier ((-κ)*x.2.2^2) θ) := by
  simp only [←fourier_add]
  congr 1
  unfold equation
  ring

/-- Exact factorization only for the literal UNWEIGHTED rectangular
source. No separability is claimed for an arbitrary compact weight. -/
theorem actual_original_box_product (κ : ℤ) (s₀ s₁ s₂ s₃ s₄ : Finset ℤ)
    (θ : AddCircle (1 : ℝ)) :
    originalCircleSum κ (originalBox s₀ s₁ s₂ s₃ s₄) (fun _ => 1) θ =
      (quadraticIntervalSum 1 s₀ θ*quadraticIntervalSum 1 s₁ θ)*
      ((quadraticIntervalSum (-1) s₂ θ*quadraticIntervalSum (-1) s₃ θ)*
        quadraticIntervalSum (-κ) s₄ θ) := by
  classical
  simp only [originalCircleSum,Finset.sum_apply,one_mul,originalBox,
    Finset.sum_product,actual_original_phase_product,quadraticIntervalSum]
  simp only [Finset.sum_mul,Finset.mul_sum]

end ActualOriginalFiniteBoxProduct318
