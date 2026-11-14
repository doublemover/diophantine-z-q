module
public import OriginalAffineDualSections318
public section
noncomputable section
namespace OriginalAffineDualSectionEquivalence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ base R) (q : Y ⟶ base R) (e : X ≅ Y) (he : e.hom ≫ q = p)
include he in
/-- Naturality transfers bijectivity across an actual scheme isomorphism;
original maps on BOTH coefficient coordinates and total sections are used. -/
lemma bijective_of_iso
    (h : Function.Bijective (OriginalDualSectionLift318.lift R q)) :
    Function.Bijective (OriginalDualSectionLift318.lift R p) := by
  let a : Γ(Y,⊤) ≃+* Γ(X,⊤) := (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  let b : Γ(thickening R q,⊤) ≃+* Γ(thickening R p,⊤) :=
    (Scheme.Γ.mapIso (DualThickeningIso318.iso R p q e he).op).commRingCatIsoToRingEquiv
  let d := SquareZeroRingLift318.congr a
  have hd : ∀ z, OriginalDualSectionLift318.lift R p (d z) =
      b (OriginalDualSectionLift318.lift R q z) := by
    intro z
    exact (OriginalDualSectionLift318.naturality R p q e.hom he z).symm
  have hn : (OriginalDualSectionLift318.lift R p : _ → _) =
      b ∘ OriginalDualSectionLift318.lift R q ∘ d.symm := by
    funext z
    have hz := hd (d.symm z)
    rw [d.apply_symm_apply] at hz
    exact hz
  rw [hn]
  exact b.bijective.comp (h.comp d.symm.bijective)
variable {q e he}
/-- Every actual affine original scheme has exactly the original two-coordinate
section ring on its actual relative thickening. No arbitrary model is substituted
for the canonical section map. -/
lemma lift_bijective [IsAffine X] : Function.Bijective (OriginalDualSectionLift318.lift R p) := by
  obtain ⟨f,hf⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  let S := Γ(X,⊤)
  letI : Algebra R S := f.hom.toAlgebra
  have hbase : X.isoSpec.hom ≫ RelativeAffineDualPresentation318.baseMap R S = p := by
    change X.isoSpec.hom ≫ Spec.map f = p
    rw [hf, Iso.hom_inv_id_assoc]
  exact bijective_of_iso R p (RelativeAffineDualPresentation318.baseMap R S) X.isoSpec hbase
    (OriginalAffineDualSections318.lift_bijective R S)
@[expose] def equivalence [IsAffine X] : SquareZeroUnit318.Dual Γ(X,⊤) ≃+* Γ(thickening R p,⊤) :=
  RingEquiv.ofBijective (OriginalDualSectionLift318.lift R p) (lift_bijective R p)
lemma equivalence_apply [IsAffine X] (x : SquareZeroUnit318.Dual Γ(X,⊤)) :
    equivalence R p x = OriginalDualSectionLift318.lift R p x := rfl
/-- Reduction of the ACTUAL inverse coordinate is the actual zero-section map. -/
lemma inverse_fst [IsAffine X] (x : Γ(thickening R p,⊤)) :
    ((equivalence R p).symm x).fst = (reduction R p).appTop x := by
  have h := OriginalDualSectionLift318.reduction_lift R p ((equivalence R p).symm x)
  change (reduction R p).appTop (equivalence R p ((equivalence R p).symm x)) = _ at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm
end OriginalAffineDualSectionEquivalence318
