module
public import RelativeFppfCoefficientRestriction318
public section
noncomputable section
namespace RelativeClassCoefficientValues318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
universe u
variable {C S R B : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S) (b : B ⟶ R)
local notation "q" => pullback.snd p r
local notation "e" => RelativeAmbientReassociation318.comparison p r b
/-- Reassociation and its inverse cancel on the ACTUAL original line
class, before passing to either relative quotient or sheafification. -/
lemma pulled (L : Class (pullback p (b ≫ r))) :
    RelativeClassCoefficientComparison318.toOriginal p r b
      (classMap (pullback.snd q b) (LineClassPullbackHom318.pullback e.hom L))=
        classMap (pullback.snd p (b ≫ r)) L := by
  rw [RelativeClassCoefficientComparison318.on_class,←MonoidHom.comp_apply,
    ←LineClassPullbackHom318.composition,Iso.inv_hom_id,LineClassPullbackHom318.identity]
  rfl
lemma original (L : Class (pullback p r)) :
    RelativeClassCoefficientComparison318.toOriginal p r b
      (classMap (pullback.snd q b) (LineClassPullbackHom318.pullback (pullback.fst q b) L))=
    testMap p r (b ≫ r) b rfl (classMap (pullback.snd p r) L) := by
  rw [RelativeClassCoefficientComparison318.on_class,testMap_class,
    ←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,
    RelativeAmbientReassociationInverse318.relative_projection]
end RelativeClassCoefficientValues318
