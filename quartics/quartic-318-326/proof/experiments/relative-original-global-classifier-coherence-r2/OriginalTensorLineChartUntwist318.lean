module
public import ContactOriginalTwistingLine318
public import OriginalTensorRightUnit318
public section
noncomputable section
namespace OriginalTensorLineChartUntwist318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L N : Line X) (U : X.Opens)
  (e : N.object.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- A genuine full-open twist frame untwists the actual original tensor
module through its canonical restriction comparison and original tensor
unit isomorphism. The old line is unchanged on the whole open. -/
@[expose] def iso : (LineSheafTensor318.line L N).object.restrict U.ι ≅ L.object.restrict U.ι :=
  TensorOpenRestriction318.iso U.ι L.object N.object ≪≫
    TensorSheafFunctor318.congr (Iso.refl (L.object.restrict U.ι)) e ≪≫
    OriginalTensorRightUnit318.iso (L.object.restrict U.ι)

/-- On every whole-open subchart and every original pure section, untwisting
is exactly scalar multiplication by the specified twist-frame coefficient. -/
lemma pure (W : U.toScheme.Opens)
    (m : Γ(L.object,U.ι.opensFunctor.obj W)) (n : Γ(N.object,U.ι.opensFunctor.obj W)) :
    (iso L N U e).hom.app W
      (IntrinsicTensorSheaf318.pure L.object N.object (U.ι.opensFunctor.obj W) m n) =
        (e.hom.app W n) • m := by
  change (OriginalTensorRightUnit318.iso (L.object.restrict U.ι)).hom.app W
    ((TensorSheafFunctor318.congr (Iso.refl (L.object.restrict U.ι)) e).hom.app W
      ((TensorOpenRestriction318.iso U.ι L.object N.object).hom.app W
        (IntrinsicTensorSheaf318.pure L.object N.object (U.ι.opensFunctor.obj W) m n))) = _
  rw [TensorSheafNormalization318.restriction_pure,TensorSheafNormalization318.congr_pure]
  exact OriginalTensorRightUnit318.pure (L.object.restrict U.ι) W m (e.hom.app W n)


lemma hom_inv : (iso L N U e).hom ≫ (iso L N U e).inv = 𝟙 _ := (iso L N U e).hom_inv_id
lemma inv_hom : (iso L N U e).inv ≫ (iso L N U e).hom = 𝟙 _ := (iso L N U e).inv_hom_id

variable (c : Fin 4 → ℚˣ) (K : Line (ContactProjectiveModel318.model c)) (d : ℤ)

def finiteIso : (ContactOriginalTwistingLine318.twist c K d).object.restrict
    (ContactOriginalWholeRestriction318.finiteOpen c).ι ≅
      K.object.restrict (ContactOriginalWholeRestriction318.finiteOpen c).ι :=
  iso K (ContactOriginalTwistingLine318.line c d) _ (ContactOriginalTwistingLine318.finiteFrame c d)

def infinityIso : (ContactOriginalTwistingLine318.twist c K d).object.restrict
    (ContactOriginalWholeRestriction318.infinityOpen c).ι ≅
      K.object.restrict (ContactOriginalWholeRestriction318.infinityOpen c).ι :=
  iso K (ContactOriginalTwistingLine318.line c d) _ (ContactOriginalTwistingLine318.infinityFrame c d)
end OriginalTensorLineChartUntwist318
