module
public import ContactGeometricIsomRelationWitness318
public section
noncomputable section
namespace ContactAffinePicardRelationWitness318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "B" => Over.mk (baseMap R)
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
variable (T : Over (Spec (CommRingCat.of ℚ))) (f : T ⟶ B)
local notation "m" => RelativeLineClassBaseChange318.totalMap p (baseMap R) T.hom f.left f.w
/-- The actual original Cartesian family behind EVERY site arrow is
compared with the parameter's canonical p-first family, with full frames
in both directions. Neither family is replaced by field-valued points. -/
@[expose] def frameEquivalence :
    {z : T.left ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K //
      z ≫ ContactGeometricIsomRelationWitness318.projection R c L K=f.left} ≃
    Frames (LineSheafPullback318.line m D) :=
  (ContactWholeSchemeFrameParameter318.equivalence R c D T.left f.left).trans
    (CartesianFrameModelEquivalence318.equivalence D m (pullback.snd p T.hom)
      (pullback.snd p (baseMap R)) f.left
      (RelativeSchemeCoefficient318.cartesian p (baseMap R) T.hom f.left f.w))
/-- The exact original absolute equality sieve on an affine coefficient
pair is the EXISTENCE-OF-POINTS relation of a concrete original scheme.
No bijection of all sheaf isomorphisms or represented quotient is inferred. -/
lemma membership :
    Presheaf.equalizerSieve
      (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from classOf L)
      (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from classOf K) f ↔
    Nonempty {z : T.left ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K //
      z ≫ ContactGeometricIsomRelationWitness318.projection R c L K=f.left} := by
  rw [OriginalPicardAbsoluteEquality318.line_membership]
  constructor
  · rintro ⟨e⟩
    exact ⟨(frameEquivalence R c L K T f).symm
      (OriginalPulledDifferenceFrameWitness318.frameOfIso m L K e)⟩
  · rintro ⟨z⟩
    exact ⟨OriginalPulledDifferenceFrameWitness318.isoOfFrame m L K
      (frameEquivalence R c L K T f z)⟩
/-- The same concrete geometric witnesses consume the actual bounded
Cartier difference Abel fiber, not a related divisor support relation. -/
lemma bounded_membership
    (A E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B)) :
    ContactDifferenceAbsoluteRelation318.sieve c B A E f ↔
    Nonempty {z : T.left ⟶ ContactGeometricIsomRelationWitness318.parameter R c
      (ContactDifferenceNaiveClass318.line c B A) (ContactDifferenceNaiveClass318.line c B E) //
      z ≫ ContactGeometricIsomRelationWitness318.projection R c
        (ContactDifferenceNaiveClass318.line c B A) (ContactDifferenceNaiveClass318.line c B E)=f.left} :=
  membership R c (ContactDifferenceNaiveClass318.line c B A)
    (ContactDifferenceNaiveClass318.line c B E) T f
end ContactAffinePicardRelationWitness318
