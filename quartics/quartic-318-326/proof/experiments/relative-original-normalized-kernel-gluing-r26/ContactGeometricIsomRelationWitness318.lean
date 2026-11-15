module
public import OriginalPulledDifferenceFrameWitness318
public section
noncomputable section
namespace ContactGeometricIsomRelationWitness318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
abbrev parameter := ContactAllAffineFrameClassifier318.parameter R c D
abbrev projection := ContactAllAffineFrameClassifier318.projection R c D
variable (T : Scheme.{0}) (b : T ⟶ Spec R)
@[expose] def isomorphism
    (x : {x : T ⟶ parameter R c L K // x ≫ projection R c L K=b}) :
    (LineSheafPullback318.line (pullback.fst p b) L).object ≅
      (LineSheafPullback318.line (pullback.fst p b) K).object :=
  OriginalPulledDifferenceFrameWitness318.isoOfFrame (pullback.fst p b) L K
    (ContactWholeSchemeFrameParameter318.equivalence R c D T b x)
@[expose] def pointOfIso
    (e : (LineSheafPullback318.line (pullback.fst p b) L).object ≅
      (LineSheafPullback318.line (pullback.fst p b) K).object) :
    {x : T ⟶ parameter R c L K // x ≫ projection R c L K=b} :=
  (ContactWholeSchemeFrameParameter318.equivalence R c D T b).symm
    (OriginalPulledDifferenceFrameWitness318.frameOfIso (pullback.fst p b) L K e)
/-- An ACTUAL fixed scheme with geometric maps witnesses exactly the
varying original full-line isomorphism RELATION on every whole test.
This is existence of points, not a claim that its points biject all isomorphisms. -/
lemma nonempty_iff :
    Nonempty {x : T ⟶ parameter R c L K // x ≫ projection R c L K=b} ↔
      Nonempty ((LineSheafPullback318.line (pullback.fst p b) L).object ≅
        (LineSheafPullback318.line (pullback.fst p b) K).object) :=
  ⟨fun ⟨x⟩ => ⟨isomorphism R c L K T b x⟩,fun ⟨e⟩ => ⟨pointOfIso R c L K T b e⟩⟩
/-- The source of witnesses has the already proved original universal
full difference frame. Thus these are genuine geometric relation witnesses. -/
@[expose] def universalFrame :
    Frames (LineSheafPullback318.line (pullback.fst p (projection R c L K)) D) :=
  ContactUniversalFrameClassifier318.universal R c D
end ContactGeometricIsomRelationWitness318
