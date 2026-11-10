module
public import OriginalRestrictedFrameScalar318
public import ContactOriginalTwistTransition318
public section
noncomputable section
namespace ContactOriginalWholeTwistScalar318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
variable (c : Fin 4 → ℚˣ) (d : ℤ)
abbrev overlap := finiteOpen c ⊓ infinityOpen c

/-- The unchanged left and right actual twist frames, genuinely restricted
to the ENTIRE original overlap. -/
def finiteFrame := OriginalRestrictedFrameScalar318.leftFrame (line c d).object
  (finiteOpen c) (overlap c) inf_le_left (ContactOriginalTwistingLine318.finiteFrame c d).symm
def infinityFrame := OriginalRestrictedFrameScalar318.rightFrame (line c d).object
  (infinityOpen c) (overlap c) inf_le_right (ContactOriginalTwistingLine318.infinityFrame c d).symm

def scalarTop : Γ((overlap c).toScheme,⊤) :=
  (LineFrameTopScalar318.ringTop (overlap c)).inv (scalar c (LaurentPolynomial.T d))

/-- Actual refined frame maps differ by the genuine original T^d scalar.
The coefficient equation is supplied by the existing clutched pullback
condition, not as an additional premise of this Contact theorem. -/
lemma frame_change : (finiteFrame c d).inv = (infinityFrame c d).inv ≫
    ModuleScalar318.map (SheafOfModules.unit (overlap c).toScheme.ringCatSheaf) (scalarTop c d) :=
  OriginalRestrictedFrameScalar318.frame_change (line c d).object
    (finiteOpen c) (infinityOpen c) (overlap c) inf_le_left inf_le_right
    (ContactOriginalTwistingLine318.finiteFrame c d).symm
    (ContactOriginalTwistingLine318.infinityFrame c d).symm
    (transitionUnit c d) (ContactOriginalTwistTransition318.inverse_relation c d)

/-- Full original tensor-frame comparison on the whole overlap, valid for
ANY original coefficient module there. The scalar is precisely T^d pulled
through the original projection and original whole-open ring isomorphisms. -/
lemma tensor_change (M : (overlap c).toScheme.Modules) :
    (OriginalTensorFrameChange318.iso M ((line c d).object.restrict (overlap c).ι)
      (finiteFrame c d).symm).hom =
    (OriginalTensorFrameChange318.iso M ((line c d).object.restrict (overlap c).ι)
      (infinityFrame c d).symm).hom ≫ ModuleScalar318.map M (scalarTop c d) :=
  OriginalTensorFrameChange318.scalar_change M _ _ _ _ (frame_change c d)
end ContactOriginalWholeTwistScalar318
