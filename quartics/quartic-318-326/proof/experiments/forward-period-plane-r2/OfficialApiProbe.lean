module
import Mathlib.Geometry.Manifold.LocalDiffeomorph
open scoped Manifold ContDiff
noncomputable section
example (h : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ω) (x : ℝ) : h.toPartialDiffeomorph x = h x := by
  unfold Diffeomorph.toPartialDiffeomorph
  rfl
example (h : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ω) (x : ℝ) : h.toPartialDiffeomorph.symm x = h.symm x := by
  unfold Diffeomorph.toPartialDiffeomorph
  rfl
example (f g : ℝ → ℝ) (x : ℝ) (hf : IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) ω f x)
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) ω g (f x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) ω (g ∘ f) x := by
  exact IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ)) (P := ℝ) hf hg
