module
public import ContactOriginalOverlapLaurentScalar318
public import OriginalRestrictionTopScalar318
public section
noncomputable section
namespace ContactOriginalTensorOverlapCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalCohomologyCoordinates318
open ContactOriginalTwistingLine318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c)) (d : ℤ)
abbrev W := finiteOpen c ⊓ infinityOpen c

/-- Actual tensor untwisting maps on the ENTIRE original overlap, with
the two original finite/infinity frames restricted canonically to it. -/
def leftIso : (twist c L d).object.restrict (W c).ι ≅ L.object.restrict (W c).ι :=
  TensorOpenRestriction318.iso (W c).ι L.object (line c d).object ≪≫
    OriginalTensorFrameChange318.iso (L.object.restrict (W c).ι) ((line c d).object.restrict (W c).ι)
      (ContactOriginalWholeTwistScalar318.finiteFrame c d).symm

def rightIso : (twist c L d).object.restrict (W c).ι ≅ L.object.restrict (W c).ι :=
  TensorOpenRestriction318.iso (W c).ι L.object (line c d).object ≪≫
    OriginalTensorFrameChange318.iso (L.object.restrict (W c).ι) ((line c d).object.restrict (W c).ι)
      (ContactOriginalWholeTwistScalar318.infinityFrame c d).symm

lemma original_square : (leftIso c L d).hom = (rightIso c L d).hom ≫
    ModuleScalar318.map (L.object.restrict (W c).ι) (ContactOriginalWholeTwistScalar318.scalarTop c d) := by
  have h := ContactOriginalWholeTwistScalar318.tensor_change c d (L.object.restrict (W c).ι)
  exact (congrArg (fun q => (TensorOpenRestriction318.iso (W c).ι L.object (line c d).object).hom ≫ q) h).trans
    (Category.assoc _ _ _).symm

def leftCoordinates (s : Γ((twist c L d).object.restrict (W c).ι,⊤)) :=
  overlapCoordinates c L (OriginalRestrictionTopScalar318.moduleTop L.object (W c)
    ((leftIso c L d).hom.app ⊤ s))
def rightCoordinates (s : Γ((twist c L d).object.restrict (W c).ι,⊤)) :=
  overlapCoordinates c L (OriginalRestrictionTopScalar318.moduleTop L.object (W c)
    ((rightIso c L d).hom.app ⊤ s))

/-- Literal Laurent matrix-scalar identity on EVERY original full-overlap
tensor section, derived from the actual clutched frames, canonical tensor
unit and original Laurent coefficient action. No matrix equation is input. -/
lemma monomial_square (s : Γ((twist c L d).object.restrict (W c).ι,⊤)) :
    leftCoordinates c L d s = (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
      rightCoordinates c L d s := by
  have h := congrArg (fun q => q.app ⊤ s) (original_square c L d)
  change (leftIso c L d).hom.app ⊤ s =
    (ModuleScalar318.map (L.object.restrict (W c).ι)
      (ContactOriginalWholeTwistScalar318.scalarTop c d)).app ⊤ ((rightIso c L d).hom.app ⊤ s) at h
  unfold leftCoordinates
  rw [h,OriginalRestrictionTopScalar318.multiply]
  change overlapCoordinates c L
    (((LineFrameTopScalar318.ringTop (W c)).hom
      ((LineFrameTopScalar318.ringTop (W c)).inv (scalar c (LaurentPolynomial.T d)))) •
        OriginalRestrictionTopScalar318.moduleTop L.object (W c) ((rightIso c L d).hom.app ⊤ s)) = _
  rw [Iso.inv_hom_id_apply]
  exact ContactOriginalOverlapLaurentScalar318.coordinates_monomial c L d _
end ContactOriginalTensorOverlapCoordinates318
