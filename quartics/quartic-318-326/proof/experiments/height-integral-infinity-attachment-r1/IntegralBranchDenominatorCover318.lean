module
public import IntegralSourceBranches318
public section
noncomputable section
namespace IntegralBranchDenominatorCover318
open Polynomial FourRootPivot318 IntegralSourceBranches318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
variable (R : Type*) [CommRing R]
@[expose] def untwisted (i : Fin 4) : R[X] :=
  ∏ j : Fin 3, (X - C (contacts R (indices i j.succ)))
@[expose] def weight : Fin 4 → ℤ := ![2700000,-2470629,5,-229376]
@[expose] def separationInteger : ℤ := 2276931686400000

/-- The original Lagrange identity with all denominators cleared over Z.
It holds over every coefficient ring, without polynomial function extensionality. -/
theorem cleared_unity :
    ∑ i : Fin 4, C (weight i : R) * untwisted R i = C (separationInteger : R) := by
  norm_num [weight,untwisted,indices,contacts,separationInteger,
    Fin.sum_univ_succ,Fin.prod_univ_succ]
  <;> ring

/-- The exceptional coefficient primes of this literal cover identity are
exactly among 2,3,5,7; no additional prime is silently discarded. -/
theorem separationInteger_factor : separationInteger = 2^15 * 3^3 * 5^5 * 7^7 := by
  norm_num [separationInteger]

theorem separation_unit (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (h5 : IsUnit (5 : R)) (h7 : IsUnit (7 : R)) :
    IsUnit (separationInteger : R) := by
  rw [separationInteger_factor]
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using
    (((h2.pow 15).mul (h3.pow 3)).mul (h5.pow 5)).mul (h7.pow 7)

variable (c : Fin 4 → Rˣ)
@[expose] def twistUnit (i : Fin 4) : Rˣ := ∏ j : Fin 3, c (indices i j.succ)
@[expose] def twisted (i : Fin 4) : R[X] :=
  ∏ j : Fin 3, coefficient R c (indices i j.succ)
@[expose] def denominator (i : Fin 4) : SourceOrder R c :=
  algebraMap R[X] (SourceOrder R c) (twisted R c i)

lemma twisted_factor (i : Fin 4) :
    twisted R c i = C (twistUnit R c i : R) * untwisted R i := by
  simp only [twisted,coefficient,LinearRootCoordinate318.parameter,
    Finset.prod_mul_distrib,←map_prod,twistUnit,untwisted]
  simp

lemma untwisted_from_twisted (i : Fin 4) :
    untwisted R i = C (↑(twistUnit R c i)⁻¹ : R) * twisted R c i := by
  rw [twisted_factor,←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul]

/-- These are the genuine branch-open denominators after the exact original
four-root regrouping, not unrelated elements with a numerical cover identity. -/
theorem regroup_denominator (i : Fin 4) :
    sourceRegroup R c i (denominator R c i) =
      algebraMap (BranchBase R c i) (RegroupedOrder R c i)
        (IntegralBranchChart318.denominator (c i) (contacts R i)
          (otherTwist R c i) (otherContact R i)) := by
  rw [denominator,AlgEquiv.commutes]
  simp only [twisted,IntegralBranchChart318.denominator,IntegralBranchChart318.other,
    otherTwist,otherContact,coefficient,map_prod,
    ←IsScalarTower.algebraMap_apply R[X] (BranchBase R c i) (RegroupedOrder R c i)]

/-- Actual integral contact denominators cover the entire original affine
four-root source whenever the explicit separation integer is invertible. -/
theorem span_top (hN : IsUnit (separationInteger : R)) :
    Ideal.span (Set.range (denominator R c)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _
    ((hN.map (algebraMap R R[X])).map (algebraMap R[X] (SourceOrder R c)))
  have h := congrArg (algebraMap R[X] (SourceOrder R c)) (cleared_unity R)
  rw [map_sum] at h
  rw [←h]
  apply Ideal.sum_mem
  intro i _
  rw [map_mul,untwisted_from_twisted R c i,map_mul]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨i,rfl⟩

end IntegralBranchDenominatorCover318
