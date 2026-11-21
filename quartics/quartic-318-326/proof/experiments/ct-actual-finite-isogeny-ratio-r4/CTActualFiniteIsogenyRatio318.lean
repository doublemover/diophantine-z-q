module
public import CTActualRetainedScalarDimensions318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualFiniteIsogenyRatio318

open CTActualRetainedScalarDimensions318 CTActualFiniteIsogenyLinear318
open CTActualGloballyFiniteIsogenySelmer318 CTActualRetainedScalarPair318
open CTActualRetainedLocalOrthogonality318 CTActualDiagonalIsotropic318
open CTFiniteIsogenyOrthogonalCount318 ActualNaturalAllPlacesFinite318
open OriginalCasselsNaturalPrimeValuation318
open Module
open scoped BigOperators

private def threeIndex (n : ℕ) (hn : 0<n) : Support n :=
  ⟨3,Nat.mem_primeFactors.mpr ⟨Nat.prime_three,dvd_mul_of_dvd_left (by decide : 3∣6) n,
    mul_ne_zero (by decide) hn.ne'⟩⟩

/-- The nontrivial inert primes of this exact support count, with 2
and 3 treated separately as fixed local places. -/
def inertAt (n : ℕ) (i : Support n) : Prop :=
  i.val≠2 ∧ i.val≠3 ∧ i.val%3≠1

private instance (n : ℕ) (i : Support n) : Decidable (inertAt n i) :=
  inferInstanceAs (Decidable (i.val≠2 ∧ i.val≠3 ∧ i.val%3≠1))

def actualInertCount (n : ℕ) : ℕ :=
  ∑ i : Support n, if inertAt n i then 1 else 0

theorem inert_index_iff (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) (i : Support n) :
    inertAt n i ↔ i.val∈n.primeFactors ∧ i.val%3=2 := by
  have hp := Nat.prime_of_mem_primeFactors i.property
  constructor
  · rintro ⟨h2,h3,hA⟩
    have hN := retained_not23_is_divisor n hn i.val hp i.property h2 h3
    have h3nd : ¬3∣i.val := by
      intro h
      rcases (Nat.dvd_prime hp).mp h with h|h
      · norm_num at h
      · exact h3 h.symm
    have hM : i.val%3≠0 := by
      intro h
      exact h3nd (Nat.dvd_iff_mod_eq_zero.mpr h)
    exact ⟨hN,by omega⟩
  · rintro ⟨hm,hA⟩
    obtain ⟨h2,h3⟩ := selected_primeFactors_ne_two_three hn hr hm
    exact ⟨h2,h3,by omega⟩

private theorem dimension_deficit (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    finrank F₂ (globalDiagonal n)=finrank F₂ (localProduct .forward n hn)+2+actualInertCount n := by
  rw [diagonal_dimension,forward_product_dimension n hn hs hr]
  have hPoint (i : Support n) :
      primeForwardDim i.val+(if inertAt n i then 1 else 0)+
        (if i=threeIndex n hn then (1:ℕ) else 0)=1 := by
    by_cases h2 : i.val=2
    · have h3 : i≠threeIndex n hn := by
        intro h
        have hh : i.val=3 := congrArg Subtype.val h
        omega
      simp [primeForwardDim,inertAt,h2,h3]
    · by_cases h3 : i.val=3
      · have hI : i=threeIndex n hn := Subtype.ext h3
        simp [primeForwardDim,inertAt,h2,h3,hI]
      · have hI : i≠threeIndex n hn := fun h => h3 (congrArg Subtype.val h)
        by_cases hS : i.val%3=1 <;> simp [primeForwardDim,inertAt,h2,h3,hI,hS]
  have h0 : (∑ i : Support n,
      (primeForwardDim i.val+(if inertAt n i then 1 else 0)+
        (if i=threeIndex n hn then (1:ℕ) else 0)))=Fintype.card (Support n) := by simp [hPoint]
  have h3 : (∑ i : Support n,if i=threeIndex n hn then (1:ℕ) else 0)=1 := by simp
  unfold actualInertCount
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,h3] at h0
  omega

/-- The diagonal is its own annihilator for the actual signed
rational reciprocity form, not a cardinality proxy. -/
theorem actual_diagonal_self_annihilator (n : ℕ) (hn : 0<n) :
    (retainedForm n).orthogonal (globalDiagonal n)=globalDiagonal n := by
  apply self_annihilator_of_half (retainedForm n) (retainedForm_nondegenerate n)
    (globalDiagonal n) (actual_diagonal_isotropic n hn)
  rw [diagonal_dimension,retained_dimension n hn]

abbrev finiteSelmerDim (e : Side) (n : ℕ) (hn : 0<n) : ℕ :=
  finrank F₂ (globalDiagonal n ⊓ localProduct e n hn : Submodule F₂ (RetainedSpace n))

/-- Exact signed dimension difference on the two native finite
all-place isogeny Selmer intersections. -/
theorem actual_finite_isogeny_dimension_difference (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    (finiteSelmerDim .forward n hn:ℤ)-(finiteSelmerDim .reverse n hn:ℤ)=
      -((2+actualInertCount n:ℕ):ℤ) := by
  have h := finite_ratio_exponent (retainedForm n) (retainedForm_nondegenerate n)
    (globalDiagonal n) (localProduct .forward n hn) (localProduct .reverse n hn)
    (actual_diagonal_self_annihilator n hn) (retained_local_complement n hn hs hr)
  have hd := dimension_deficit n hn hs hr
  change (finiteSelmerDim .forward n hn:ℤ)-(finiteSelmerDim .reverse n hn:ℤ)=
    (finrank F₂ (localProduct .forward n hn):ℤ)-(finrank F₂ (globalDiagonal n):ℤ) at h
  omega

private theorem actual_selmer_card (e : Side) (n : ℕ) (hn : 0<n) :
    Nat.card (scalarSelmer e n hn)=2^(finiteSelmerDim e n hn) :=
  (Nat.card_congr (scalarSelmerIntersection e n hn)).trans (card_eq_two_pow_dim _)

/-- Actual finite isogeny scalar Selmer cardinality ratio 2^(−2−k₂).
This multiplication form avoids any possible zero-denominator convention.
The forward side is the exactly verified scalar image, while its
identification with continuous forward connecting cocycles is separate. -/
theorem actual_finite_isogeny_ratio (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    Nat.card (scalarSelmer .reverse n hn)=
      2^(2+actualInertCount n)*Nat.card (scalarSelmer .forward n hn) := by
  rw [actual_selmer_card .reverse n hn,actual_selmer_card .forward n hn]
  have h := actual_finite_isogeny_dimension_difference n hn hs hr
  have he : finiteSelmerDim .reverse n hn=(2+actualInertCount n)+finiteSelmerDim .forward n hn := by omega
  rw [he,pow_add]

end CTActualFiniteIsogenyRatio318

#print axioms CTActualFiniteIsogenyRatio318.actual_diagonal_self_annihilator
#print axioms CTActualFiniteIsogenyRatio318.actual_finite_isogeny_dimension_difference
#print axioms CTActualFiniteIsogenyRatio318.actual_finite_isogeny_ratio
