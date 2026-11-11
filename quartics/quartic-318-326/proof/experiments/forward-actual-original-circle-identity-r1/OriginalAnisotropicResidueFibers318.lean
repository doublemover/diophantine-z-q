module
public import OriginalReducedResidueBounds318
public section
noncomputable section
namespace OriginalAnisotropicResidueFibers318
open scoped BigOperators
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318
open IntegerResidueBoxCount318 OriginalReducedResidueBounds318
set_option maxHeartbeats 4500000

@[expose] def Rectangle (A B C : ℕ) := Interval A×Interval B×Interval C
@[expose] def coordinates {A B C : ℕ} (a : Rectangle A B C) : Vector ℤ :=
  (a.1.1,a.2.1.1,a.2.2.1)
@[expose] def ResidueRectangle (A B C p : ℕ) [NeZero p] (S : Finset (Vector (ZMod p))) :=
  {a : Rectangle A B C // reduce p (coordinates a)∈S}

lemma self_residue_divides (p : ℕ) [NeZero p] (x : ℤ) :
    (p:ℤ)∣x-((x:ZMod p).val:ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,sub_self]

/-- Exact anisotropic residue-fiber estimate, retaining all three integer
boundary terms rather than replacing the rectangle by a large cube. -/
theorem rectangle_residue_count (A B C p : ℕ) [NeZero p] (hp : 0<p)
    (S : Finset (Vector (ZMod p))) :
    Nat.card (ResidueRectangle A B C p S)≤
      S.card*(2*A/p+1)*(2*B/p+1)*(2*C/p+1) := by
  classical
  let Target := Σ y : ↥S,
    ResidueBox A p (y.1.1.val:ℤ)×ResidueBox B p (y.1.2.1.val:ℤ)×ResidueBox C p (y.1.2.2.val:ℤ)
  let f : ResidueRectangle A B C p S → Target := fun a =>
    ⟨⟨reduce p (coordinates a.1),a.2⟩,
      ⟨a.1.1,self_residue_divides p a.1.1.1⟩,
      ⟨a.1.2.1,self_residue_divides p a.1.2.1.1⟩,
      ⟨a.1.2.2,self_residue_divides p a.1.2.2.1⟩⟩
  let forget : Target → Vector ℤ := fun a => (a.2.1.1.1,a.2.2.1.1.1,a.2.2.2.1.1)
  have hi : Function.Injective f := by
    intro a b he
    have hh := congrArg forget he
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hh)
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun c : Vector ℤ => c.2.1) hh)
      · exact Subtype.ext (congrArg (fun c : Vector ℤ => c.2.2) hh)
  have hc := Nat.card_le_card_of_injective f hi
  have htarget : Nat.card Target≤S.card*((2*A/p+1)*((2*B/p+1)*(2*C/p+1))) := by
    change Nat.card (Σ y : ↥S,
      ResidueBox A p (y.1.1.val:ℤ)×ResidueBox B p (y.1.2.1.val:ℤ)×ResidueBox C p (y.1.2.2.val:ℤ))≤_
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    calc
      _ = ∑ y : ↥S, Nat.card (ResidueBox A p (y.1.1.val:ℤ))*
          (Nat.card (ResidueBox B p (y.1.2.1.val:ℤ))*Nat.card (ResidueBox C p (y.1.2.2.val:ℤ))) := by
        simp only [Fintype.card_prod,Nat.card_eq_fintype_card]
      _ ≤ ∑ _y : ↥S, (2*A/p+1)*((2*B/p+1)*(2*C/p+1)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact Nat.mul_le_mul (residue_box_card A p hp _)
          (Nat.mul_le_mul (residue_box_card B p hp _) (residue_box_card C p hp _))
      _ = _ := by simp
  calc
    _ ≤ S.card*((2*A/p+1)*((2*B/p+1)*(2*C/p+1))) := hc.trans htarget
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual reduced polynomial common-zero fibers in the same anisotropic
coefficient rectangle; this is a concrete per-prime sieve bound, not an
assumed density estimate or a global large-prime-tail assertion. -/
theorem original_slice_rectangle_bounds (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : OriginalControlledIntegralBasis318.IntegralBasisTriple
      (LiteralSliceModulus318.prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣label)
    (A B C : ℕ) :
    Nat.card (ResidueRectangle A B C p (reducedFirst p κ label u v z))≤
      8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1) ∧
    Nat.card (ResidueRectangle A B C p (reducedSecond p κ label u v z))≤
      8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1) := by
  obtain ⟨hfirst,hsecond⟩ := original_slice_residue_bounds κ label s u v z hb p hκ ht
  have hp : 0<p := (Fact.out : p.Prime).pos
  constructor
  · exact (rectangle_residue_count A B C p hp _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfirst)))
  · exact (rectangle_residue_count A B C p hp _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsecond)))

end OriginalAnisotropicResidueFibers318
