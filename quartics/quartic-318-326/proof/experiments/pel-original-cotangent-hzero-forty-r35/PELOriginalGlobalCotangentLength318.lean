module
public import FourRootCotangentWholeSupport318
public import FourRootZeroAllPoints318
public import Mathlib.Algebra.BigOperators.Finprod
public section
noncomputable section
namespace PELOriginalGlobalCotangentLength318
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open PELOriginalCommonContactBase318 FourRootGluedDerivativeIdeal318
/-- Actual canonical local-ring length at EVERY scheme point, including
nonclosed and generic points. This is not an indicator definition. -/
def length (x : FourRootGluedScheme318.scheme branches) : ℕ∞ :=
  FourRootCotangentStalkQuotient318.length branches x
lemma on_zero (z : zeroScheme branches) : length (into branches z) = 1 := by
  rw [←PELOriginalZeroAllPoints318.originalEquiv_point z]
  exact PELOriginalCotangentSheafLength318.branch_length
    (PELOriginalZeroAllPoints318.originalEquiv z).val
    (PELOriginalZeroAllPoints318.originalEquiv z).property
/-- Exact entire scheme-theoretic support of the actual cotangent
stalk-length function, not only equality on complex-valued points. -/
theorem support_eq : Function.support length = Set.range (into branches) := by
  ext x
  constructor
  · intro hx
    by_contra hn
    exact hx (FourRootCotangentWholeSupport318.outside_length_zero branches branches_injective x hn)
  · rintro ⟨z,rfl⟩
    change length (into branches z) ≠ 0
    rw [on_zero]
    exact one_ne_zero
theorem support_finite : (Function.support length).Finite := by
  rw [support_eq]
  exact Set.finite_range _
/-- The sum of ACTUAL local-ring cotangent stalk lengths over the
ENTIRE original scheme is40. Finite support and zero at all other
scheme primes were proved before this full-space sum is taken. -/
theorem total_length_forty : (∑ᶠ x : FourRootGluedScheme318.scheme branches, length x) = 40 := by
  classical
  letI : Fintype (zeroScheme branches) := Fintype.ofFinite _
  let s := Finset.univ.image (into branches)
  have hs : Function.support length ⊆ (s : Set (FourRootGluedScheme318.scheme branches)) := by
    rw [support_eq]
    rintro _ ⟨z,rfl⟩
    exact Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩
  calc
    (∑ᶠ x, length x) = ∑ x ∈ s, length x := finsum_eq_sum_of_support_subset length hs
    _ = ∑ z : zeroScheme branches, length (into branches z) := by
      apply Finset.sum_image
      intro a _ b _ h
      exact (into branches).isClosedEmbedding.injective h
    _ = 40 := by
      have hc : Fintype.card (zeroScheme branches) = 40 := by
        simpa only [Nat.card_eq_fintype_card] using PELOriginalZeroAllPoints318.card_forty
      simp_rw [on_zero]
      simp [hc]
end PELOriginalGlobalCotangentLength318
