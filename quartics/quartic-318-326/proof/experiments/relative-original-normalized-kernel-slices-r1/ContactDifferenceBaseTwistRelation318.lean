module
public import ContactDifferenceNaiveClass318
public section
noncomputable section
namespace ContactDifferenceBaseTwistRelation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ) (B : Over (Spec (CommRingCat.of ℚ)))
  (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def sieve : Sieve B :=
  Presheaf.equalizerSieve (ContactDifferenceNaiveClass318.value c B D) (ContactDifferenceNaiveClass318.value c B E)
/-- Membership retains actual whole line isomorphisms after one actual
base line, on arbitrary further tests including nonreduced bases. -/
lemma membership (T : Over (Spec (CommRingCat.of ℚ))) (f : T ⟶ B) : sieve c B D E f ↔
    ∃ M : Line T.left,Nonempty
      ((LineSheafTensor318.line
        (LineSheafPullback318.line (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w)
          (ContactDifferenceNaiveClass318.line c B D))
        (LineSheafPullback318.line (pullback.snd p T.hom) M)).object ≅
        (LineSheafPullback318.line (RelativeLineClassBaseChange318.totalMap p B.hom T.hom f.left f.w)
          (ContactDifferenceNaiveClass318.line c B E)).object) := by
  change (RelativeLineClassBaseChange318.presheaf p).map f.op (ContactDifferenceNaiveClass318.value c B D)=
    (RelativeLineClassBaseChange318.presheaf p).map f.op (ContactDifferenceNaiveClass318.value c B E) ↔ _
  rw [ContactDifferenceNaiveClass318.restricted,ContactDifferenceNaiveClass318.restricted]
  exact RelativeClassBaseTwistIso318.iff_relative (pullback.snd p T.hom) _ _
/-- Exact actual fppf Abel fibers, characterized by a covering whole-line
base-twist isomorphism relation rather than support or field values. -/
lemma abel_iff_covering : (ContactCartierDifferenceAbel318.transformation c).app (op B) D=
    (ContactCartierDifferenceAbel318.transformation c).app (op B) E ↔
      sieve c B D E ∈ RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) B := by
  rw [←ContactDifferenceNaiveClass318.sheaf_value,←ContactDifferenceNaiveClass318.sheaf_value]
  exact OriginalFppfClassEquality318.iff_covering p B _ _
end ContactDifferenceBaseTwistRelation318
