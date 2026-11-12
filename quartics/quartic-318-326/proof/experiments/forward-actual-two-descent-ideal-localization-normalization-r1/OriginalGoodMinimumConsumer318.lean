module
public import OriginalGoodLatticeVolumeBound318
public section
noncomputable section
namespace OriginalGoodMinimumConsumer318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalAttainedMinima318 OriginalControlledIntegralBasis318
open OriginalThreeDimensionalTransference318 OriginalGoodLatticeVolumeBound318
open OriginalAnisotropicRectangle318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An independent original triple cannot lie in the plane spanned by two
original vectors. This checks the exact space where third minimality is
consumed, rather than identifying minima merely by their labels. -/
lemma independent_outside_plane (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v : Vector ℤ) (f : Fin 3 → Vector ℤ) (hf : IndependentTriple p κ t f) :
    ∃ i, embed (f i)∉Submodule.span ℝ (Set.range ![embed u,embed v]) := by
  classical
  by_contra h
  push_neg at h
  let S := Submodule.span ℝ (Set.range ![embed u,embed v])
  let g : Fin 3 → S := fun i => ⟨embed (f i),h i⟩
  have hg : LinearIndependent ℝ g := LinearIndependent.of_comp S.subtype hf.2
  have h3 := hg.fintype_card_le_finrank
  have h2 := finrank_range_le_card (R := ℝ) ![embed u,embed v]
  change 3≤Module.finrank ℝ S at h3
  change Module.finrank ℝ S≤2 at h2
  omega

/-- Exact complement of the SAME LargeThird predicate used by the bad-
lattice tail. No separately defined or assumed 'good minimum' is inserted. -/
theorem complementary_good_count (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) (T R : ℝ) (hTR : T≤R)
    (hgood : ¬LargeThird p κ t T) :
    (Nat.card (NormPoints p κ t R):ℝ)*(FixedSquarefreeCRT318.modulus p:ℝ)^2≤5202*R^3 := by
  classical
  unfold LargeThird at hgood
  push_neg at hgood
  obtain ⟨f,hf,hfT⟩ := hgood
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis p hp κ t
  obtain ⟨i,hiout⟩ := independent_outside_plane p κ t u v f hf
  have hwT : ‖embed w‖≤T := (hwmin (f i) (hf.1 i) hiout).trans (hfT i)
  exact good_lattice_count p hp hd hp2 κ t u v w z hb huv hvw hip hz hwmin R (hwT.trans hTR)

/-- Original retained slice-prime specialization with the same odd
modulus and original factor2 conventions as the bad-lattice estimate. -/
theorem actual_slice_good_count (κ label : ℤ)
    (t : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (T R : ℝ) (hTR : T≤R)
    (hgood : ¬LargeThird (LiteralSliceModulus318.prime κ label) κ t T) :
    (Nat.card (NormPoints (LiteralSliceModulus318.prime κ label) κ t R):ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2≤5202*R^3 := by
  simpa only [LiteralSliceModulus318.modulus] using
    complementary_good_count (LiteralSliceModulus318.prime κ label)
      (LiteralSliceModulus318.prime_is_prime κ label) (LiteralSliceModulus318.prime_injective κ label)
      (LiteralSliceModulus318.prime_odd κ label) κ t T R hTR hgood

end OriginalGoodMinimumConsumer318
