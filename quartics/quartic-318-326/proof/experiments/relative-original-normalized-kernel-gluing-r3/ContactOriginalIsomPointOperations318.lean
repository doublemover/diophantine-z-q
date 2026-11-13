module
public import OriginalNativeIsomPullback318
public section
noncomputable section
namespace ContactOriginalIsomPointOperations318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M : Line (curve R c)) {T : Scheme.{0}} (b : T ⟶ Spec R)
@[expose] def identity : Points R c L L b :=
  ContactGeometricIsomRelationWitness318.pointOfIso R c L L T b (Iso.refl _)
@[expose] def inverse (z : Points R c L K b) : Points R c K L b :=
  ContactGeometricIsomRelationWitness318.pointOfIso R c K L T b
    (ContactWholeIsomPointEquivalence318.equivalence R c L K T b z).symm
@[expose] def composition (z : Points R c L K b) (w : Points R c K M b) :
    Points R c L M b :=
  ContactGeometricIsomRelationWitness318.pointOfIso R c L M T b
    (ContactWholeIsomPointEquivalence318.equivalence R c L K T b z ≪≫
      ContactWholeIsomPointEquivalence318.equivalence R c K M T b w)
lemma recover_identity :
    ContactWholeIsomPointEquivalence318.equivalence R c L L T b (identity R c L b)=
      Iso.refl _ := ContactWholeIsomPointEquivalence318.recover_classify R c L L T b _
lemma recover_inverse (z : Points R c L K b) :
    ContactWholeIsomPointEquivalence318.equivalence R c K L T b (inverse R c L K b z)=
      (ContactWholeIsomPointEquivalence318.equivalence R c L K T b z).symm :=
  ContactWholeIsomPointEquivalence318.recover_classify R c K L T b _
lemma recover_composition (z : Points R c L K b) (w : Points R c K M b) :
    ContactWholeIsomPointEquivalence318.equivalence R c L M T b
      (composition R c L K M b z w)=
    ContactWholeIsomPointEquivalence318.equivalence R c L K T b z ≪≫
      ContactWholeIsomPointEquivalence318.equivalence R c K M T b w :=
  ContactWholeIsomPointEquivalence318.recover_classify R c L M T b _
end ContactOriginalIsomPointOperations318
