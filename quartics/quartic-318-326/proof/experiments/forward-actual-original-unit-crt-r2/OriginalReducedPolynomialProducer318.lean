module
public import OriginalReducedPolynomialEquiv318
public section
noncomputable section
namespace OriginalReducedPolynomialProducer318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open OriginalCofactorCoordinates318 LiteralSievePolynomial318 LiteralSecondSievePolynomial318
open OriginalReducedPolynomialEquiv318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def rationalVector (u : Vector ℤ) : Vector ℚ := ((u.1:ℚ),(u.2.1:ℚ),(u.2.2:ℚ))

lemma triple_cast (u v z : Vector ℤ) :
    triple (rationalVector u) (rationalVector v) (rationalVector z)=(determinant u v z:ℚ) := by
  simp [triple,cross,rationalVector,determinant,OriginalIntegerNormalProjection318.normal,
    LiteralIntegerDuality318.dot]

/-- Actual reduced-basis substitution, retaining its original integer
vectors and the exact rational polynomial ring of the source sieve. -/
@[expose] def substitution (u v z : Vector ℤ) : Poly →ₐ[ℚ] Poly :=
  forward (rationalVector u) (rationalVector v) (rationalVector z)

lemma substitution_evaluation (u v z c : Vector ℤ) (f : Poly) :
    MvPolynomial.eval ![(c.1:ℚ),(c.2.1:ℚ),(c.2.2:ℚ)] (substitution u v z f)=
      MvPolynomial.eval ![((synthesis u v z c).1:ℚ),((synthesis u v z c).2.1:ℚ),
        ((synthesis u v z c).2.2:ℚ)] f := by
  rw [substitution,forward_evaluation]
  congr 1
  funext i
  fin_cases i <;> simp [rationalVector,synthesis,zsmul_eq_mul,mul_comm]

/-- Both original rational polynomial pairs remain relatively prime in
THIS SAME constructed reduced basis. The inverse algebra equivalence
supplies IsLocalHom; a bare substitution hom is not treated as enough. -/
theorem original_pairs_relPrime (q : ι → ℕ) (hq : ∀ i, (q i).Prime)
    (κ : ℤ) (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2)
    (label : ℤ) (hκ : κ≠0) (ht : label≠0) :
    IsRelPrime (substitution u v z (firstP (κ:ℚ) (label:ℚ)))
      (substitution u v z (productD (label:ℚ))) ∧
    IsRelPrime (substitution u v z (secondP (κ:ℚ) (label:ℚ)))
      (substitution u v z (productD (label:ℚ))) := by
  have hd : triple (rationalVector u) (rationalVector v) (rationalVector z)≠0 := by
    rw [triple_cast]
    exact_mod_cast determinant_ne_zero q hq κ s u v z hb huv hip
  have hκQ : (κ:ℚ)≠0 := by exact_mod_cast hκ
  have htQ : (label:ℚ)≠0 := by exact_mod_cast ht
  exact ⟨preserves_relPrime _ _ _ hd _ _ (first_pair_relPrime (κ:ℚ) (label:ℚ) htQ),
    preserves_relPrime _ _ _ hd _ _ (second_pair_relPrime (κ:ℚ) (label:ℚ) hκQ htQ)⟩

/-- One whole reduced basis simultaneously carries every required
primewise K-content witness AND both exact rational coprime pairs. -/
theorem actual_same_basis_sieve_inputs (κ label : ℤ) (hκ : κ≠0) (ht : label≠0)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i))) :
    ∃ u v w z : Vector ℤ,
      IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z ∧
      ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧ ‖embed z‖≤2*‖embed w‖ ∧
      IsRelPrime (substitution u v z (firstP (κ:ℚ) (label:ℚ)))
        (substitution u v z (productD (label:ℚ))) ∧
      IsRelPrime (substitution u v z (secondP (κ:ℚ) (label:ℚ)))
        (substitution u v z (productD (label:ℚ))) ∧
      (∀ R : ℝ, ‖embed w‖≤R →
        (Nat.card (OriginalAnisotropicRectangle318.NormPoints
          (LiteralSliceModulus318.prime κ label) κ s R):ℝ)*
          (LiteralSliceModulus318.modulus κ label:ℝ)^2≤5202*R^3) ∧
      ∀ p : ℕ, p.Prime → ¬(p:ℤ)∣label →
        ∃ c : Vector ℤ, ¬(p:ℤ)∣LiteralAdjacentNormSlice318.K κ label (synthesis u v z c) := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis
    (LiteralSliceModulus318.prime κ label) (LiteralSliceModulus318.prime_is_prime κ label) κ s
  obtain ⟨hfirst,hsecond⟩ := original_pairs_relPrime (LiteralSliceModulus318.prime κ label)
    (LiteralSliceModulus318.prime_is_prime κ label) κ s u v z hb huv hip label hκ ht
  refine ⟨u,v,w,z,hb,huv,hvw,hz,hfirst,hsecond,?_,?_⟩
  · intro R hR
    exact OriginalGoodLatticeVolumeBound318.good_lattice_count
      (LiteralSliceModulus318.prime κ label) (LiteralSliceModulus318.prime_is_prime κ label)
      (LiteralSliceModulus318.prime_injective κ label) (LiteralSliceModulus318.prime_odd κ label)
      κ s u v w z hb huv hvw hip hz hwmin R hR
  · intro p hprime hp
    letI : Fact p.Prime := ⟨hprime⟩
    exact OriginalReducedContentProducer318.actual_reduced_K_nonzero κ label s u v z hb p hp

end OriginalReducedPolynomialProducer318
