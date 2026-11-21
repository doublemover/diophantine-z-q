module
public import ActualGaussianWeberSelectedGaussianPrime318
public import Mathlib.SetTheory.Cardinal.Finite
public section
noncomputable section

namespace ActualGaussianWeberChosenPlaceLift318

open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318

variable {p : ℕ} [Fact p.Prime]
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Algebra GaussianInt S]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable (w : HeightOneSpectrum S)

abbrev OverPlace := valuationSubringAtPrime L w

@[expose] def integralOverI : OverPlace (L:=L) w :=
  algebraMap S (OverPlace (L:=L) w) (algebraMap GaussianInt S gaussianI)

theorem integralOverI_sq : (integralOverI (L:=L) w)^2=(-1:OverPlace (L:=L) w) := by
  have h := congrArg ((algebraMap S (OverPlace (L:=L) w)).comp (algebraMap GaussianInt S)) gaussianI_sq
  simpa only [RingHom.comp_apply,integralOverI,map_pow,map_neg,map_one] using h

/-- Literal residue of the original Gaussian integer at the fixed
integral extension prime, not an arbitrary map of residue fields. -/
@[expose] def rawResidue : GaussianInt→+*ResidueField (OverPlace (L:=L) w) :=
  (residue (OverPlace (L:=L) w)).comp
    ((algebraMap S (OverPlace (L:=L) w)).comp (algebraMap GaussianInt S))

theorem rawResidue_zero_iff (z : GaussianInt) :
    rawResidue (L:=L) w z=0 ↔ z∈w.asIdeal.under GaussianInt := by
  change residue (OverPlace (L:=L) w)
    (algebraMap S (OverPlace (L:=L) w) (algebraMap GaussianInt S z))=0 ↔ _
  rw [residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (OverPlace (L:=L) w) w.asIdeal
    (algebraMap GaussianInt S z)

theorem rawResidue_respects (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj)
    (z : GaussianInt) (hz : z∈selectedIdeal j hj) :
    rawResidue (L:=L) w z=0 :=
  (rawResidue_zero_iff (L:=L) w z).mpr (hUnder.symm ▸ hz)

/-- The prime-field embedding at the actual over-place, formed by
quotienting the literal Gaussian residue map and using the selected
degree-one generator identification in the reverse direction. -/
@[expose] def chosenEmbedding (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj) :
    ZMod p→+*ResidueField (OverPlace (L:=L) w) :=
  (Ideal.Quotient.lift (selectedIdeal j hj) (rawResidue (L:=L) w)
    (rawResidue_respects (L:=L) w j hj hUnder)).comp
    (quotientEquiv j hj).symm.toRingHom

theorem chosenEmbedding_reduce (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj) (z : GaussianInt) :
    chosenEmbedding (L:=L) w j hj hUnder (reduce j hj z)=rawResidue (L:=L) w z := by
  change Ideal.Quotient.lift (selectedIdeal j hj) (rawResidue (L:=L) w)
    (rawResidue_respects (L:=L) w j hj hUnder) ((quotientEquiv j hj).symm (reduce j hj z))=_
  rw [←quotientEquiv_mk j hj z,RingEquiv.symm_apply_apply,Ideal.Quotient.lift_mk]

/-- The *same* chosen root is the residue of the same integral i in
the actual extension valuation. This distinguishes the conjugate
prime without any subsequent sign choice. -/
theorem chosenEmbedding_i (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj) :
    chosenEmbedding (L:=L) w j hj hUnder j=
      residue (OverPlace (L:=L) w) (integralOverI (L:=L) w) := by
  simpa only [reduce_i,rawResidue,integralOverI,RingHom.comp_apply] using
    (chosenEmbedding_reduce (L:=L) w j hj hUnder gaussianI)

theorem contracted_card (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj) :
    Nat.card (GaussianInt ⧸ w.asIdeal.under GaussianInt)=p := by
  let e := (Ideal.quotEquivOfEq hUnder).trans (quotientEquiv j hj)
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,ZMod.card]

theorem actual_residue_char (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj) :
    CharP (ResidueField (OverPlace (L:=L) w)) p :=
  ⟨fun n => by
    let f := chosenEmbedding (L:=L) w j hj hUnder
    have h : (n:ResidueField (OverPlace (L:=L) w))=0 ↔ (n:ZMod p)=0 := by
      rw [←map_natCast f n,←map_zero f,f.injective.eq_iff]
    exact h.trans (CharP.cast_eq_zero_iff (ZMod p) p n)⟩

/-- Exact prime-to-p condition at this very place; no separate
invertibility assumption on the chosen torsion modulus. -/
theorem modulus_nonzero (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj)
    (M : ℕ) (hM : ¬ p∣M) :
    residue (OverPlace (L:=L) w) (M:OverPlace (L:=L) w)≠0 := by
  letI := actual_residue_char (L:=L) w j hj hUnder
  rw [map_natCast]
  exact fun h => hM ((CharP.cast_eq_zero_iff (ResidueField (OverPlace (L:=L) w)) p M).mp h)

theorem residue_two_ne (j : ZMod p) (hj : j^2= -1)
    (hUnder : w.asIdeal.under GaussianInt=selectedIdeal j hj)
    (h2 : (2:ZMod p)≠0) : (2:ResidueField (OverPlace (L:=L) w))≠0 := by
  intro h
  apply h2
  apply (chosenEmbedding (L:=L) w j hj hUnder).injective
  simpa only [map_ofNat,map_zero] using h

end ActualGaussianWeberChosenPlaceLift318
