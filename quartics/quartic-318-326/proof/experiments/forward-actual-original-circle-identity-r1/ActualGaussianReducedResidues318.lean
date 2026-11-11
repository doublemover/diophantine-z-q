module
public import ActualSecondChartResidues318
public section
noncomputable section
namespace ActualGaussianReducedResidues318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 TernaryCongruenceLattices318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318 OriginalReducedBasisResidues318
open LiteralAdjacentNormSlice318 OriginalReducedResidueBounds318 ActualSecondChartResidues318
set_option maxHeartbeats 6500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Genuine second-source quartic after the SAME actual integral basis
map. The original label t and original modulus remain unchanged. -/
@[expose] def reducedActual (p : ℕ) [Fact p.Prime] (κ t : ℤ) (u v z : Vector ℤ) :
    Finset (Vector (ZMod p)) := Finset.univ.filter (fun c =>
      P' (κ:ZMod p) (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0 ∧
      K (κ:ZMod p) (t:ZMod p) (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c)=0)

theorem actual_basis_bound (q : ι → ℕ) (κ t : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (p : ℕ) [Fact p.Prime] (hM : ¬(p:ℤ)∣(FixedSquarefreeCRT318.modulus q:ℤ))
    (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣t) : (reducedActual p κ t u v z).card≤8*p := by
  classical
  have hi := fieldSynthesis_injective q κ s u v z hb p hM
  have hk : (κ:ZMod p)≠0 := fun h => hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp h)
  have ht' : (t:ZMod p)≠0 := fun h => ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp h)
  let f : ↥(reducedActual p κ t u v z) → ↥(actualZeros (κ:ZMod p) (t:ZMod p)) := fun c =>
    ⟨fieldSynthesis (reduce p u) (reduce p v) (reduce p z) c.1,by
      simpa only [actualZeros,reducedActual,Finset.mem_filter,Finset.mem_univ,true_and] using c.2⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  have hc : (reducedActual p κ t u v z).card≤(actualZeros (κ:ZMod p) (t:ZMod p)).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hf
  exact hc.trans (by simpa only [ZMod.card] using actual_card (κ:ZMod p) (t:ZMod p) hk ht')

/-- Original q(t), including its exact index and bad-prime exclusion,
is consumed here. No q(t+2), new prime avoidance, or reselected basis. -/
theorem original_label_basis_bound (κ t : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ t) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣t) :
    (reducedActual p κ t u v z).card≤8*p := by
  apply actual_basis_bound (LiteralSliceModulus318.prime κ t) κ t s u v z hb p _ hκ ht
  intro h
  exact ht (dvd_trans h (LiteralSliceModulus318.modulus_divides_label κ t))

end ActualGaussianReducedResidues318
