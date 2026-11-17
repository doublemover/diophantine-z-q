module
public import OriginalPicardAbsoluteEquality318
public import ContactDifferenceNaiveClass318
public section
noncomputable section
namespace ContactDifferenceAbsoluteRelation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ) (B : Over (Spec (CommRingCat.of ℚ)))
  (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def sieve : Sieve B :=
  Presheaf.equalizerSieve
    (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from
      classOf (ContactDifferenceNaiveClass318.line c B D))
    (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from
      classOf (ContactDifferenceNaiveClass318.line c B E))
/-- Full original bounded-difference Abel fiber relation, now with no
base-line twist witness left in membership. Equality is local, not global. -/
lemma membership (T : Over (Spec (CommRingCat.of ℚ))) (f : T ⟶ B) : sieve c B D E f ↔
    Nonempty ((LineSheafPullback318.line
      (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w)
      (ContactDifferenceNaiveClass318.line c B D)).object ≅
      (LineSheafPullback318.line
        (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w)
        (ContactDifferenceNaiveClass318.line c B E)).object) :=
  OriginalPicardAbsoluteEquality318.line_membership p B T f _ _
lemma abel_iff_covering :
    (ContactCartierDifferenceAbel318.transformation c).app (op B) D=
      (ContactCartierDifferenceAbel318.transformation c).app (op B) E ↔
      sieve c B D E ∈ RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) B := by
  rw [←ContactDifferenceNaiveClass318.sheaf_value,←ContactDifferenceNaiveClass318.sheaf_value]
  exact OriginalPicardAbsoluteEquality318.iff_covering p B _ _
end ContactDifferenceAbsoluteRelation318
