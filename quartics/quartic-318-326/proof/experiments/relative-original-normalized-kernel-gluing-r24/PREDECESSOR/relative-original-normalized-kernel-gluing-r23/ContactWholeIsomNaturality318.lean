module
public import OriginalPulledDifferencePath318
public import ContactWholeIsomPointEquivalence318
public section
noncomputable section
namespace ContactWholeIsomNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c L K
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L K
variable {T T' : Scheme.{0}} (b : T ⟶ Spec R) (b' : T' ⟶ Spec R)
  (h : T' ⟶ T) (hh : h ≫ b=b')
abbrev Isoms (t : T ⟶ Spec R) :=
  (LineSheafPullback318.line (pullback.fst p t) L).object ≅
    (LineSheafPullback318.line (pullback.fst p t) K).object
abbrev Points (t : T ⟶ Spec R) := {z : T ⟶ P // z ≫ q=t}
/-- The transition is literal native module pullback along the actual
base-changed family map, then the original coefficient-path associators. -/
@[expose] def pullIso (e : Isoms R c L K b) : Isoms R c L K b' :=
  OriginalPulledDifferencePath318.pullIso
    (RelativeSchemeCoefficient318.map p b b' h hh)
    (pullback.fst p b) (pullback.fst p b') (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) L K e
@[expose] def pointMap (z : Points R c L K b) : Points R c L K b' :=
  ⟨h ≫ z.val,by rw [Category.assoc,z.property,hh]⟩
/-- The EXACT old classifying point of a full original isomorphism is
natural for every coefficient arrow, with no affine/flat/reduced premise. -/
lemma classify (e : Isoms R c L K b) :
    ContactGeometricIsomRelationWitness318.pointOfIso R c L K T' b'
      (pullIso R c L K b b' h hh e)=
    pointMap R c L K b b' h hh
      (ContactGeometricIsomRelationWitness318.pointOfIso R c L K T b e) := by
  apply Subtype.ext
  change ContactWholeSchemeFrameParameter318.classifyingMap R c D T' b'
      (OriginalPulledDifferenceFrameWitness318.frameOfIso (pullback.fst p b') L K
        (pullIso R c L K b b' h hh e))=
    h ≫ ContactWholeSchemeFrameParameter318.classifyingMap R c D T b
      (OriginalPulledDifferenceFrameWitness318.frameOfIso (pullback.fst p b) L K e)
  rw [←OriginalPulledDifferencePath318.frameOfIso]
  exact ContactUniversalFrameClassifier318.classify_natural R c D T T' b b' h hh
    (OriginalPulledDifferenceFrameWitness318.frameOfIso (pullback.fst p b) L K e)
/-- Full recovery, not merely nonemptiness of the isomorphism relation,
commutes with the SAME native coefficient pullback on all whole tests. -/
lemma recovery (z : Points R c L K b) :
    pullIso R c L K b b' h hh (ContactWholeIsomPointEquivalence318.equivalence R c L K T b z)=
    ContactWholeIsomPointEquivalence318.equivalence R c L K T' b'
      (pointMap R c L K b b' h hh z) := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T' b').symm.injective
  change ContactGeometricIsomRelationWitness318.pointOfIso R c L K T' b' _=
    ContactGeometricIsomRelationWitness318.pointOfIso R c L K T' b' _
  rw [classify,ContactWholeIsomPointEquivalence318.classify_recover,
    ContactWholeIsomPointEquivalence318.classify_recover]
end ContactWholeIsomNaturality318
