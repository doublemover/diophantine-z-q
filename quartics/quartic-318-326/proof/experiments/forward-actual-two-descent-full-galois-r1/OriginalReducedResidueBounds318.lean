module
public import OriginalSecondResidueCount318
public section
noncomputable section
namespace OriginalReducedResidueBounds318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 TernaryCongruenceLattices318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318 OriginalReducedBasisResidues318
open LiteralAdjacentNormSlice318 OriginalQuadraticResidueCount318 OriginalSecondResidueCount318
set_option maxHeartbeats 4500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def fieldSynthesis {F : Type*} [CommRing F] (u v z c : Vector F) : Vector F :=
  (u.1*c.1+v.1*c.2.1+z.1*c.2.2,
    u.2.1*c.1+v.2.1*c.2.1+z.2.1*c.2.2,
    u.2.2*c.1+v.2.2*c.2.1+z.2.2*c.2.2)

lemma reduction_synthesis (p : ℕ) (u v z c : Vector ℤ) :
    reduce p (synthesis u v z c)=fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c) := by
  apply Prod.ext
  · simp [reduce,synthesis,fieldSynthesis,zsmul_eq_mul,mul_comm]
  · apply Prod.ext <;> simp [reduce,synthesis,fieldSynthesis,zsmul_eq_mul,mul_comm]

/-- Actual finite-field coordinate map is a permutation, obtained from
constructed residue surjectivity and finiteness of the SAME residue space. -/
theorem fieldSynthesis_injective (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (p : ℕ) [Fact p.Prime] (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ)) :
    Function.Injective (fieldSynthesis (reduce p u) (reduce p v) (reduce p z)) := by
  apply Finite.injective_iff_surjective.mpr
  intro y
  obtain ⟨c,hc⟩ := residue_surjective q κ s u v z hb p hM y
  exact ⟨reduce p c,by rwa [←reduction_synthesis]⟩

@[expose] def reducedFirst (p : ℕ) [Fact p.Prime] (κ t : ℤ) (u v z : Vector ℤ) : Finset (Vector (ZMod p)) :=
  Finset.univ.filter (fun c =>
    P (κ:ZMod p) (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0 ∧
    D (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0)
@[expose] def reducedSecond (p : ℕ) [Fact p.Prime] (κ t : ℤ) (u v z : Vector ℤ) : Finset (Vector (ZMod p)) :=
  Finset.univ.filter (fun c =>
    P' (κ:ZMod p) (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0 ∧
    D (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0)

/-- Uniform8p common-zero bounds in the ACTUAL reduced coefficients,
including every exceptional original second-pair fiber. -/
theorem actual_reduced_residue_bounds (q : ι → ℕ) (κ t : ℤ)
    (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) (p : ℕ) [Fact p.Prime]
    (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ))
    (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣t) :
    (reducedFirst p κ t u v z).card≤8*p ∧ (reducedSecond p κ t u v z).card≤8*p := by
  classical
  have hi := fieldSynthesis_injective q κ s u v z hb p hM
  have hk : (κ:ZMod p)≠0 := fun h => hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp h)
  have ht' : (t:ZMod p)≠0 := fun h => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
  let f : ↥(reducedFirst p κ t u v z) → ↥(firstZeros (κ:ZMod p) (t:ZMod p)) := fun c =>
    ⟨fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c.1,by
      simpa only [firstZeros,reducedFirst,Finset.mem_filter,Finset.mem_univ,true_and] using c.2⟩
  let g : ↥(reducedSecond p κ t u v z) → ↥(secondZeros (κ:ZMod p) (t:ZMod p)) := fun c =>
    ⟨fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c.1,by
      simpa only [secondZeros,reducedSecond,Finset.mem_filter,Finset.mem_univ,true_and] using c.2⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  have hg : Function.Injective g := fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  have hc1 : (reducedFirst p κ t u v z).card≤(firstZeros (κ:ZMod p) (t:ZMod p)).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hf
  have hc2 : (reducedSecond p κ t u v z).card≤(secondZeros (κ:ZMod p) (t:ZMod p)).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective g hg
  exact ⟨hc1.trans (by simpa only [ZMod.card] using firstZeros_card (κ:ZMod p) (t:ZMod p) hk),
    hc2.trans (by simpa only [ZMod.card] using secondZeros_card (κ:ZMod p) (t:ZMod p) hk ht')⟩

/-- The original slice label produces the entire permitted prime range;
no new modulus or local-content exclusion is supplied by the consumer. -/
theorem original_slice_residue_bounds (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣label) :
    (reducedFirst p κ label u v z).card≤8*p ∧ (reducedSecond p κ label u v z).card≤8*p := by
  apply actual_reduced_residue_bounds (LiteralSliceModulus318.prime κ label) κ label s u v z hb p _ hκ ht
  intro h
  exact ht (dvd_trans h (LiteralSliceModulus318.modulus_divides_label κ label))

end OriginalReducedResidueBounds318
