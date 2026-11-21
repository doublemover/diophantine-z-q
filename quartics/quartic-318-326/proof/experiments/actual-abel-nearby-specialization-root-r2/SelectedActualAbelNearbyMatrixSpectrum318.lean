module

public import SelectedActualAbelNearbySpecializationRoot318
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

public section

open Filter Polynomial Topology
open scoped Topology

namespace SelectedActualAbelNearbyMatrixSpectrum318

open SelectedActualAbelNearbySpecializationRoot318

/-- Specializing the literal polynomial multiplication matrix preserves
the existence of a spectral value near any prescribed spectral value
of its limiting fibre. This is a determinant assertion about the actual
whole matrix (with multiplicities), not a claim about a chosen branch or
about realization of the values by characters of the algebra. -/
theorem eventually_det_zero_near (ι : Type*) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ[X]) (z₀ u : ℂ)
    (h : (Matrix.scalar ι u - M.map (Polynomial.evalRingHom z₀)).det = 0)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ z in 𝓝 z₀, ∃ a : ℂ,
      (Matrix.scalar ι a - M.map (Polynomial.evalRingHom z)).det = 0 ∧ ‖u - a‖ < r := by
  have hroot : (M.charpoly.map (Polynomial.evalRingHom z₀)).IsRoot u := by
    change (M.charpoly.map (Polynomial.evalRingHom z₀)).eval u = 0
    rw [← Matrix.charpoly_map M (Polynomial.evalRingHom z₀), Matrix.eval_charpoly]
    exact h
  refine (eventually_specialized_root_near M.charpoly (Matrix.charpoly_monic M)
    z₀ u hroot r hr).mono ?_
  intro z hz
  obtain ⟨a,ha,hd⟩ := hz
  have he : (M.charpoly.map (Polynomial.evalRingHom z)).eval a = 0 := ha
  rw [← Matrix.charpoly_map M (Polynomial.evalRingHom z), Matrix.eval_charpoly] at he
  exact ⟨a,he,hd⟩

end SelectedActualAbelNearbyMatrixSpectrum318

#print axioms SelectedActualAbelNearbyMatrixSpectrum318.eventually_det_zero_near
