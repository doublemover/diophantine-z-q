module
public import SchemeIsoPullbackFullyFaithful318
public import RelativeFamilyFrameEquivalence318
public section
noncomputable section
namespace OriginalFrameIsoEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y : Scheme.{u}}
@[expose] def target {L M : Line X} (e : L.object ≅ M.object) : Frames L ≃ Frames M where
  toFun a := a ≪≫ e
  invFun b := b ≪≫ e.symm
  left_inv a := by apply Iso.ext; simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  right_inv b := by apply Iso.ext; simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
variable (f : X ⟶ Y) [IsIso f] (L : Line Y)
/-- Actual full frames are preserved AND reflected by an original scheme
isomorphism; the forward map is the unchanged native frame pullback. -/
@[expose] def equivalence : Frames L ≃ Frames (LineSheafPullback318.line f L) :=
  (SchemeIsoPullbackFullyFaithful318.fullyFaithful f).isoEquiv.trans
    {toFun := fun e => (IdentityCotangent318.pullbackUnitIso f).symm ≪≫ e
     invFun := fun e => IdentityCotangent318.pullbackUnitIso f ≪≫ e
     left_inv := by intro e; apply Iso.ext; simp only [Iso.trans_hom,Iso.symm_hom,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
     right_inv := by intro e; apply Iso.ext; simp only [Iso.trans_hom,Iso.symm_hom,←Category.assoc,Iso.inv_hom_id,Category.id_comp]}
lemma forward (e : Frames L) : equivalence f L e=OriginalFramePullback318.frame f L e := rfl
end OriginalFrameIsoEquivalence318
