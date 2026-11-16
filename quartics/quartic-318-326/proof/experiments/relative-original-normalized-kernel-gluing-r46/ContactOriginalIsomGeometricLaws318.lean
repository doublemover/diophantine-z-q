module
public import ContactOriginalIsomGeometricComposition318
public section
noncomputable section
namespace ContactOriginalIsomGeometricLaws318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomGeometricComposition318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c))
local notation "P" => ContactGeometricIsomRelationWitness318.parameter R c
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
@[expose] def leftUnitMap : P L K ⟶ pairs R c L L K :=
  pairMap R c L L K (q L K)
    (ContactOriginalIsomPointOperations318.identity R c L (q L K))
    ⟨𝟙 (P L K),Category.id_comp _⟩
@[expose] def rightUnitMap : P L K ⟶ pairs R c L K K :=
  pairMap R c L K K (q L K) ⟨𝟙 (P L K),Category.id_comp _⟩
    (ContactOriginalIsomPointOperations318.identity R c K (q L K))
lemma leftUnitMap_fst : leftUnitMap R c L K ≫ pullback.fst (q L L) (q L K)=
    q L K ≫ ContactOriginalIsomGeometricInverse318.unit R c L := by
  rw [leftUnitMap,pairMap,pullback.lift_fst]
  exact (ContactOriginalIsomGeometricInverse318.unit_evaluation R c L (q L K)).symm
lemma rightUnitMap_snd : rightUnitMap R c L K ≫ pullback.snd (q L K) (q K K)=
    q L K ≫ ContactOriginalIsomGeometricInverse318.unit R c K := by
  rw [rightUnitMap,pairMap,pullback.lift_snd]
  exact (ContactOriginalIsomGeometricInverse318.unit_evaluation R c K (q L K)).symm
lemma left_unit : leftUnitMap R c L K ≫ composition R c L L K=𝟙 (P L K) := by
  rw [leftUnitMap,evaluation,ContactOriginalIsomPointLaws318.left_identity]
lemma right_unit : rightUnitMap R c L K ≫ composition R c L K K=𝟙 (P L K) := by
  rw [rightUnitMap,evaluation,ContactOriginalIsomPointLaws318.right_identity]
/-- The actual graph of the geometric inversion in the composable-pair
fiber product. Neither coordinate is replaced by an existential witness. -/
@[expose] def inverseMap : P L K ⟶ pairs R c L K L :=
  pairMap R c L K L (q L K) ⟨𝟙 (P L K),Category.id_comp _⟩
    (ContactOriginalIsomPointOperations318.inverse R c L K (q L K)
      ⟨𝟙 (P L K),Category.id_comp _⟩)
lemma inverseMap_fst : inverseMap R c L K ≫ pullback.fst (q L K) (q K L)=𝟙 (P L K) :=
  pullback.lift_fst _ _ _
lemma inverseMap_snd : inverseMap R c L K ≫ pullback.snd (q L K) (q K L)=
    ContactOriginalIsomGeometricInverse318.inversion R c L K :=
  pullback.lift_snd _ _ _
lemma inverse_composition : inverseMap R c L K ≫ composition R c L K L=
    q L K ≫ ContactOriginalIsomGeometricInverse318.unit R c L := by
  rw [inverseMap,evaluation,ContactOriginalIsomPointLaws318.left_inverse]
  exact (ContactOriginalIsomGeometricInverse318.unit_evaluation R c L (q L K)).symm
@[expose] def reverseInverseMap : P L K ⟶ pairs R c K L K :=
  pairMap R c K L K (q L K)
    (ContactOriginalIsomPointOperations318.inverse R c L K (q L K)
      ⟨𝟙 (P L K),Category.id_comp _⟩) ⟨𝟙 (P L K),Category.id_comp _⟩
lemma reverseInverseMap_fst : reverseInverseMap R c L K ≫ pullback.fst (q K L) (q L K)=
    ContactOriginalIsomGeometricInverse318.inversion R c L K :=
  pullback.lift_fst _ _ _
lemma reverseInverseMap_snd : reverseInverseMap R c L K ≫ pullback.snd (q K L) (q L K)=𝟙 (P L K) :=
  pullback.lift_snd _ _ _
lemma reverse_inverse_composition : reverseInverseMap R c L K ≫ composition R c K L K=
    q L K ≫ ContactOriginalIsomGeometricInverse318.unit R c K := by
  rw [reverseInverseMap,evaluation,ContactOriginalIsomPointLaws318.right_inverse]
  exact (ContactOriginalIsomGeometricInverse318.unit_evaluation R c K (q L K)).symm
end ContactOriginalIsomGeometricLaws318
