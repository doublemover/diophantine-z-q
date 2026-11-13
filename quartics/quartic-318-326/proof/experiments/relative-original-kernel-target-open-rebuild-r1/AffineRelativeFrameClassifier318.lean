module
public import SchemeAffineMorphismEvaluation318
public import ContactArbitraryCoefficientFrameDescent318
public section
noncomputable section
namespace AffineRelativeFrameClassifier318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X B Y : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
abbrev Point (R : CommRingCat.{u}) (b : Spec R ⟶ B) := {x : Spec R ⟶ Y // x ≫ q=b}
def pointMap (R S : CommRingCat.{u}) (g : Spec S ⟶ Spec R)
    (b : Spec R ⟶ B) (a : Spec S ⟶ B) (hg : g ≫ b=a) (x : Point q R b) : Point q S a :=
  ⟨g ≫ x.val,by rw [Category.assoc,x.property,hg]⟩
/-- Only the AFFINE classifier is an input. Whole-scheme classification
and effective recovery will be constructed. The Contact adapter supplies this datum. -/
structure Data where
  equivalence : ∀ (R : CommRingCat.{u}) (b : Spec R ⟶ B),
    Point q R b ≃ Frames (LineSheafPullback318.line (pullback.fst p b) L)
  natural : ∀ (R S : CommRingCat.{u}) (g : Spec S ⟶ Spec R)
    (b : Spec R ⟶ B) (a : Spec S ⟶ B) (hg : g ≫ b=a) (x : Point q R b),
    OriginalFramePathTransport318.transport L (RelativeSchemeCoefficient318.map p b a g hg)
      (pullback.fst p b) (pullback.fst p a) (RelativeSchemeCoefficient318.map_fst _ _ _ _ _)
      (equivalence R b x)=equivalence S a (pointMap q R S g b a hg x)
end AffineRelativeFrameClassifier318
