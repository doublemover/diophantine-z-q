module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Int.Order.Units
public section
noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace SelectedAbelSumGramProductIntegral318

variable {g : ℕ}

abbrev rsign (R : Type*) [CommRing R] (s : Equiv.Perm (Fin g)) : R :=
  ((Equiv.Perm.sign s : ℤ) : R)

private theorem rsign_mul_self (R : Type*) [CommRing R] (s : Equiv.Perm (Fin g)) :
    rsign R s * rsign R s = 1 := by
  unfold rsign
  rw [←Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

/-- Exact conjugate-first double expansion on the ordered cross
Gram. The inner determinant is that of its transpose with columns
permuted, so the two signs cancel without assuming G is Hermitian. -/
theorem double_permutation {R : Type*} [CommRing R] (G : Matrix (Fin g) (Fin g) R) :
    (∑ s : Equiv.Perm (Fin g), ∑ t : Equiv.Perm (Fin g),
      (rsign R s * rsign R t) * ∏ k, G (s k) (t k)) =
      (g.factorial : R) * G.det := by
  calc
    _ = ∑ s : Equiv.Perm (Fin g), rsign R s * (Gᵀ.submatrix id s).det := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_assoc] <;> rfl
    _ = ∑ _s : Equiv.Perm (Fin g), G.det := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Matrix.det_permute', Matrix.det_transpose]
      change rsign R s * (rsign R s * G.det) = G.det
      rw [←mul_assoc, rsign_mul_self, one_mul]
    _ = (g.factorial : R) * G.det := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (c : Fin g → Fin g → X → ℂ)

abbrev pairIntegral : Matrix (Fin g) (Fin g) ℂ :=
  fun i j => ∫ x, c i j x ∂μ

abbrev summand (s t : Equiv.Perm (Fin g)) (z : Fin g → X) : ℂ :=
  (rsign ℂ s * rsign ℂ t) * ∏ k, c (s k) (t k) (z k)

/-- The actual analytic Fubini identity needed for the Abel sum. Input
entries are the cross densities of the same ordered differential
basis against the one chosen quotient measure. No period matrices,
synthetic volume, norm comparison, or unidentified determinant. -/
theorem integral_double_permutation [SigmaFinite μ] (hc : ∀ i j, Integrable (c i j) μ) :
    (∫ z, ∑ s : Equiv.Perm (Fin g), ∑ t : Equiv.Perm (Fin g),
      summand c s t z ∂(Measure.pi (fun _ : Fin g => μ))) =
      (g.factorial : ℂ) * (pairIntegral μ c).det := by
  let ν := Measure.pi (fun _ : Fin g => μ)
  have ht (s t : Equiv.Perm (Fin g)) : Integrable (summand c s t) ν := by
    exact (Integrable.fintype_prod (fun k : Fin g => hc (s k) (t k))).const_mul _
  have hs (s : Equiv.Perm (Fin g)) :
      Integrable (fun z => ∑ t : Equiv.Perm (Fin g), summand c s t z) ν :=
    integrable_finsetSum _ (fun t _ => ht s t)
  have hterm (s t : Equiv.Perm (Fin g)) :
      (∫ z, summand c s t z ∂ν) =
        (rsign ℂ s * rsign ℂ t) * ∏ k, pairIntegral μ c (s k) (t k) := by
    unfold summand
    rw [integral_const_mul]
    exact congrArg ((rsign ℂ s * rsign ℂ t) * ·)
      (integral_fintype_prod_eq_prod (μ := fun _ : Fin g => μ) (fun k => c (s k) (t k)))
  have hrow (s : Equiv.Perm (Fin g)) :
      (∫ z, ∑ t : Equiv.Perm (Fin g), summand c s t z ∂ν) =
        ∑ t : Equiv.Perm (Fin g), (rsign ℂ s * rsign ℂ t) *
          ∏ k, pairIntegral μ c (s k) (t k) := by
    rw [integral_finsetSum _ (fun t _ => ht s t)]
    exact Finset.sum_congr rfl (fun t _ => hterm s t)
  rw [integral_finsetSum _ (fun s _ => hs s)]
  simp only [hrow]
  exact double_permutation (pairIntegral μ c)

end SelectedAbelSumGramProductIntegral318

#print axioms SelectedAbelSumGramProductIntegral318.double_permutation
#print axioms SelectedAbelSumGramProductIntegral318.integral_double_permutation
