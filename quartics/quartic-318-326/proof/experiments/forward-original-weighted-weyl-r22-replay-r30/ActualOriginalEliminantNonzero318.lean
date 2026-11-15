module
public import ActualQuarticOffsetPolynomial318
public section
noncomputable section
namespace ActualOriginalEliminantNonzero318
open TernaryQuadraticLineCover318 OriginalControlledIntegralBasis318
open OriginalCofactorCoordinates318 OriginalBoundedIntegerShear318 OriginalBasisDeterminantIndex318
open OriginalAffineSieveEliminants318 ActualQuarticRegularNonzero318 ActualQuarticExceptionalNonzero318
open ActualQuarticOffsetPolynomial318
set_option maxHeartbeats 7500000

/-- A constant evaluation proves nonvanishing of the actual two-offset
polynomial. The exceptional label uses the actual first whole-basis vector,
whose independence from every allowed shear is certified by the unchanged
determinant. No generic position or eliminant nonvanishing input. -/
theorem from_determinant (κ t : ℤ) (hκ : κ≠0) (ht : t≠0) (u v d : Vector ℤ)
    (hdet : determinant u v d≠0) (hA : fA true κ t d≠0) : polynomial κ t u v d≠0 := by
  intro hz
  by_cases ht2 : t+2=0
  · have he : t=-2 := eq_neg_of_add_eq_zero_left ht2
    subst t
    have hh := at_first κ (-2) u v d
    rw [hz,map_zero] at hh
    exact exceptional_nonzero κ hκ u v d hdet hA hh.symm
  · have hh := at_origin κ t u v d
    rw [hz,map_zero] at hh
    exact regular_nonzero κ t d ht ht2 hA hh.symm

/-- Original q(t)^2 is the nonzero determinant producer. The shear is
chosen from the existing fixed candidate family and leaves q(t) unchanged.
A successful original quadratic leading coefficient supplies hA; no
additional excluded primes or basis choice depending on the label shift. -/
theorem actual_original_shear (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (i j : ℤ) (hA : fA true κ t (shear i j u v z)≠0) :
    polynomial κ t u v (shear i j u v z)≠0 := by
  apply from_determinant κ t hκ ht u v (shear i j u v z) _ hA
  rw [determinant_shear]
  intro hd
  have hh := actual_basis_determinant_index (LiteralSliceModulus318.prime κ t)
    (LiteralSliceModulus318.prime_is_prime κ t) (LiteralSliceModulus318.prime_injective κ t)
    (LiteralSliceModulus318.prime_odd κ t) κ s u v z hb
  have hM : (0:ℝ)<LiteralSliceModulus318.modulus κ t := by
    exact_mod_cast LiteralSliceModulus318.modulus_positive κ t
  rw [hd,Int.cast_zero,abs_zero] at hh
  exact (sq_pos_of_pos hM).ne' hh.symm

end ActualOriginalEliminantNonzero318
