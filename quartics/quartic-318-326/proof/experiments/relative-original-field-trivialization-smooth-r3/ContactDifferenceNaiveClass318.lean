module
public import OriginalFppfClassEquality318
public section
noncomputable section
namespace ContactDifferenceNaiveClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def line (B : Over (Spec (CommRingCat.of ℚ)))
    (D : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B)) : Line (pullback p B.hom) :=
  ContactCartierDifferenceLine318.line c D.1.1 D.2.1 B.hom D.1.2 D.2.2
@[expose] def value (B : Over (Spec (CommRingCat.of ℚ)))
    (D : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B)) : RelativeLineClassBaseChange318.TestClass p B.hom :=
  OriginalLineAbelTransformation318.point p B.hom (line c B D)
lemma sheaf_value (B : Over (Spec (CommRingCat.of ℚ)))
    (D : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B)) :
    (RelativeFppfLineSheaf318.unit p).app (op B) (value c B D)=
      (ContactCartierDifferenceAbel318.transformation c).app (op B) D :=
  ContactCartierDifferenceLine318.value c D.1.1 D.2.1 B.hom D.1.2 D.2.2
lemma restricted (B T : Over (Spec (CommRingCat.of ℚ))) (f : T ⟶ B)
    (D : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B)) :
    (RelativeLineClassBaseChange318.presheaf p).map f.op (value c B D)=
      OriginalLineAbelTransformation318.point p T.hom
        (LineSheafPullback318.line (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w) (line c B D)) := by
  rw [value,OriginalLineAbelTransformation318.point,RelativeLineClassBaseChange318.testMap_class]
  rfl
end ContactDifferenceNaiveClass318
