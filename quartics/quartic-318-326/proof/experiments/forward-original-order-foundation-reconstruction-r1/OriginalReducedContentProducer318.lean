module
public import OriginalReducedBasisResidues318
public section
noncomputable section
namespace OriginalReducedContentProducer318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open LiteralAdjacentNormSlice318 LiteralBasisContent318 OriginalReducedBasisResidues318
open TernaryCongruenceLattices318 LiteralSliceModulus318
set_option maxHeartbeats 3000000

/-- The original adjacent-norm K has an ACTUAL nonzero integer evaluation
in the constructed reduced coordinates at every prime outside the slice
label. The t=-2 branch uses the original nonconstant explicit witness. -/
theorem actual_reduced_K_nonzero (κ label : ℤ)
    (s : ∀ i : PrimeIndex κ label, Option (ZMod (prime κ label i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple (prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hp : ¬(p:ℤ)∣label) :
    ∃ c : Vector ℤ, ¬(p:ℤ)∣K κ label (synthesis u v z c) := by
  have ht : (label:ZMod p)≠0 := by
    intro h
    exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd label p).mp h)
  obtain ⟨y,hy⟩ := K_nonzero_value (κ:ZMod p) (label:ZMod p) ht
  obtain ⟨c,hc⟩ := original_slice_residue_surjective κ label s u v z hb p hp y
  refine ⟨c,?_⟩
  intro h
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (K κ label (synthesis u v z c)) p).mpr h
  rw [K_cast,hc] at he
  exact hy he

/-- Construct the reduced WHOLE basis once, then produce all primewise
content witnesses in that same basis. Prime-dependent bases cannot be
silently substituted into the later geometric-sieve polynomial. -/
theorem actual_reduced_basis_content (κ label : ℤ)
    (s : ∀ i : PrimeIndex κ label, Option (ZMod (prime κ label i))) :
    ∃ u v w z : Vector ℤ, IntegralBasisTriple (prime κ label) κ s u v z ∧
      ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧ ‖embed z‖≤2*‖embed w‖ ∧
      ∀ p : ℕ, p.Prime → ¬(p:ℤ)∣label →
        ∃ c : Vector ℤ, ¬(p:ℤ)∣K κ label (synthesis u v z c) := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ :=
    actual_controlled_basis (prime κ label) (prime_is_prime κ label) κ s
  refine ⟨u,v,w,z,hb,huv,hvw,hz,?_⟩
  intro p hprime hp
  letI : Fact p.Prime := ⟨hprime⟩
  exact actual_reduced_K_nonzero κ label s u v z hb p hp

end OriginalReducedContentProducer318
