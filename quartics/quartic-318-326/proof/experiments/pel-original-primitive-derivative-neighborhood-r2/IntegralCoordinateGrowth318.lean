module
public import MvPolynomialEvaluationGrowth318
public import WeightedMonicRootBound318
public section
noncomputable section
namespace IntegralCoordinateGrowth318
open Polynomial
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A finite family of actual monic coordinate equations gives one
uniform polynomial bound on ALL source coordinates in terms of the
original base vector. No chosen source point or fiber is discarded. -/
theorem exists_bound (Q : ι → Polynomial (MvPolynomial κ ℂ))
    (hm : ∀ i, (Q i).Monic) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (v : κ → ℂ) (w : ι → ℂ),
      (∀ i, ((Q i).map (MvPolynomial.eval v)).IsRoot (w i)) →
      ‖w‖ ≤ C*(1+‖v‖)^N+1 := by
  classical
  let J := Σ i : ι, Fin (Q i).natDegree
  obtain ⟨C,hC,N,hnum⟩ := MvPolynomialEvaluationGrowth318.exists_uniform_growth
    (Finset.univ : Finset J) (fun j => (Q j.1).coeff j.2.val)
  refine ⟨C,hC,N,?_⟩
  intro v w hw
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ C*(1+‖v‖)^N+1)).mpr
  intro i
  have hc : ∀ n < ((Q i).map (MvPolynomial.eval v)).natDegree,
      1 * ‖(((Q i).map (MvPolynomial.eval v)).coeff n)‖ ≤ C*(1+‖v‖)^N := by
    intro n hn
    rw [(hm i).natDegree_map] at hn
    simpa only [Polynomial.coeff_map,one_mul] using
      hnum (⟨i,⟨n,hn⟩⟩ : J) (Finset.mem_univ _) v
  have hh := WeightedMonicRootBound318.root_bound ((Q i).map (MvPolynomial.eval v))
    ((hm i).map _) 1 (C*(1+‖v‖)^N) zero_lt_one (by positivity) hc (w i) (hw i)
  simpa only [one_mul] using hh
end IntegralCoordinateGrowth318
