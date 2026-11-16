module
public import ContactOriginalIsomOperationsNaturality318
public section
noncomputable section
namespace ContactOriginalIsomGeometricInverse318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c))
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
/-- Actual identity section of the SAME original diagonal parameter. -/
@[expose] def unit : Spec R ⟶ P L L :=
  (ContactOriginalIsomPointOperations318.identity R c L (𝟙 (Spec R))).val
lemma unit_over : unit R c L ≫ q L L=𝟙 (Spec R) :=
  (ContactOriginalIsomPointOperations318.identity R c L (𝟙 (Spec R))).property
/-- Actual geometric inversion, obtained from the native full inverse of
the universal original isomorphism, not from a relation-only witness. -/
@[expose] def inversion : P L K ⟶ P K L :=
  (ContactOriginalIsomPointOperations318.inverse R c L K (q L K)
    ⟨𝟙 (P L K),Category.id_comp _⟩).val
lemma inversion_over : inversion R c L K ≫ q K L=q L K :=
  (ContactOriginalIsomPointOperations318.inverse R c L K (q L K)
    ⟨𝟙 (P L K),Category.id_comp _⟩).property
lemma unit_recovers :
    ContactWholeIsomPointEquivalence318.equivalence R c L L (Spec R) (𝟙 (Spec R))
      ⟨unit R c L,unit_over R c L⟩=Iso.refl _ :=
  ContactOriginalIsomPointOperations318.recover_identity R c L (𝟙 (Spec R))
lemma inversion_recovers :
    ContactWholeIsomPointEquivalence318.equivalence R c K L (P L K) (q L K)
      ⟨inversion R c L K,inversion_over R c L K⟩=
      (ContactUniversalOriginalIsom318.universal R c L K).symm :=
  ContactOriginalIsomPointOperations318.recover_inverse R c L K (q L K)
    ⟨𝟙 (P L K),Category.id_comp _⟩
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
lemma unit_evaluation : b ≫ unit R c L=
    (ContactOriginalIsomPointOperations318.identity R c L b).val := by
  exact congrArg Subtype.val (ContactOriginalIsomOperationsNaturality318.identity
    R c L (𝟙 (Spec R)) b b (Category.comp_id b))
/-- Evaluation is valid on EVERY whole coefficient scheme and every
original full Isom point, with no flatness or nonemptiness premise. -/
lemma inversion_evaluation (z : Points R c L K b) :
    z.val ≫ inversion R c L K=(ContactOriginalIsomPointOperations318.inverse R c L K b z).val := by
  have h := ContactOriginalIsomOperationsNaturality318.inverse R c L K
    (q L K) b z.val z.property (⟨𝟙 (P L K),Category.id_comp _⟩ : Points R c L K (q L K))
  have hz : pointMap R c L K (q L K) b z.val z.property
      (⟨𝟙 (P L K),Category.id_comp _⟩ : Points R c L K (q L K))=z := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hz] at h
  exact congrArg Subtype.val h
/-- A literal scheme-morphism involution, not merely pointwise agreement
on fields or equality of nonempty relation witnesses. -/
lemma inversion_involutive : inversion R c L K ≫ inversion R c K L=𝟙 (P L K) := by
  have h := inversion_evaluation R c K L (q L K)
    (ContactOriginalIsomPointOperations318.inverse R c L K (q L K)
      ⟨𝟙 (P L K),Category.id_comp _⟩)
  rw [ContactOriginalIsomPointLaws318.inverse_inverse] at h
  exact h
end ContactOriginalIsomGeometricInverse318
