module
public import PELOriginalRegularCoordinateAlgebra318
public import Mathlib.Algebra.Polynomial.Roots
public section
noncomputable section
namespace FourRootSignCoefficientExtraction318
open scoped BigOperators
abbrev Mask := Fin 4 → Bool
/-- Rational character, so its finite orthogonality certificate is exact. -/
def weight (m s : Mask) : ℚ := ∏ i, if m i && s i then -1 else 1

theorem orthogonality_rat : ∀ m n : Mask,
    (∑ s : Mask, weight m s * weight n s) = if m = n then 16 else 0 := by
  decide +kernel

theorem orthogonality (m n : Mask) :
    (∑ s : Mask, (weight m s : ℂ) * (weight n s : ℂ)) =
      if m = n then 16 else 0 := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) (orthogonality_rat m n)
  push_cast at h
  exact h

/-- The literal squarefree-root monomial. -/
def monomial (z : Fin 4 → ℂ) (m : Mask) : ℂ := ∏ i, if m i then z i else 1

def signed (z : Fin 4 → ℂ) (s : Mask) (i : Fin 4) : ℂ :=
  if s i then -z i else z i

lemma monomial_signed (z : Fin 4 → ℂ) (m s : Mask) :
    monomial (signed z s) m = (weight m s : ℂ) * monomial z m := by
  unfold monomial weight
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases hm : m i <;> cases hs : s i <;> simp [signed,hm,hs]

/-- Character averaging extracts each coefficient times its actual root
monomial. No degree, independence or source field is assumed. -/
theorem extract (a : Mask → ℂ) (z : Fin 4 → ℂ) (m : Mask) :
    (∑ s : Mask, (weight m s : ℂ) *
      ∑ n : Mask, a n * monomial (signed z s) n) =
      16 * (a m * monomial z m) := by
  simp_rw [monomial_signed,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ n : Mask,
      (∑ s : Mask, (weight m s : ℂ) * (a n * ((weight n s : ℂ) * monomial z n))) =
        (if m = n then 16 else 0) * (a n * monomial z n) := by
    intro n
    calc
      _ = ∑ s : Mask, ((weight m s : ℂ) * (weight n s : ℂ)) *
          (a n * monomial z n) := by apply Finset.sum_congr rfl; intro s hs; ring
      _ = (∑ s : Mask, (weight m s : ℂ) * (weight n s : ℂ)) *
          (a n * monomial z n) := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [orthogonality]
  simp_rw [hterm]
  simp

lemma monomial_ne_zero (z : Fin 4 → ℂ) (hz : ∀ i, z i ≠ 0) (m : Mask) :
    monomial z m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  cases hm : m i <;> simp [hm,hz i]

/-- Evaluation on all sixteen actual signed tuples determines every
coefficient, provided the roots at this regular base are nonzero. -/
theorem coefficients_zero (a : Mask → ℂ) (z : Fin 4 → ℂ)
    (hz : ∀ i, z i ≠ 0)
    (h : ∀ s : Mask, (∑ n : Mask, a n * monomial (signed z s) n) = 0) :
    ∀ m, a m = 0 := by
  intro m
  have he := extract a z m
  simp only [h,mul_zero,Finset.sum_const_zero] at he
  have hm : a m * monomial z m = 0 := by linear_combination -he / 16
  exact (mul_eq_zero.mp hm).resolve_right (monomial_ne_zero z hz m)

/-- Polynomial coefficients need only vanish away from the four branches.
This is an infinite subset of the actual complex base. -/
theorem polynomial_zero (b : Fin 4 → ℂ) (p : Polynomial ℂ)
    (h : ∀ t : ℂ, (∀ i, t ≠ b i) → p.eval t = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hi : Set.Infinite ((Set.univ : Set ℂ) \ Set.range b) :=
    Set.infinite_univ.diff (Set.finite_range b)
  apply hi.mono
  intro t ht
  exact h t (by intro i he; exact ht.2 ⟨i,he.symm⟩)
end FourRootSignCoefficientExtraction318
