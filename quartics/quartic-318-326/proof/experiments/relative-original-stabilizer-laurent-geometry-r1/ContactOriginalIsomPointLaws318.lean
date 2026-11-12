module
public import ContactOriginalIsomPointOperations318
public section
noncomputable section
namespace ContactOriginalIsomPointLaws318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomPointOperations318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M N : Line (curve R c)) {T : Scheme.{0}} (b : T ⟶ Spec R)
lemma left_identity (z : Points R c L K b) :
    composition R c L L K b (identity R c L b) z=z := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T b).injective
  rw [recover_composition,recover_identity,Iso.refl_trans]
lemma right_identity (z : Points R c L K b) :
    composition R c L K K b z (identity R c K b)=z := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T b).injective
  rw [recover_composition,recover_identity,Iso.trans_refl]
lemma inverse_inverse (z : Points R c L K b) :
    inverse R c K L b (inverse R c L K b z)=z := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L K T b).injective
  rw [recover_inverse,recover_inverse,Iso.symm_symm_eq]
lemma left_inverse (z : Points R c L K b) :
    composition R c L K L b z (inverse R c L K b z)=identity R c L b := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L L T b).injective
  rw [recover_composition,recover_inverse,recover_identity]
  apply Iso.ext
  exact Iso.hom_inv_id _
lemma right_inverse (z : Points R c L K b) :
    composition R c K L K b (inverse R c L K b z) z=identity R c K b := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c K K T b).injective
  rw [recover_composition,recover_inverse,recover_identity]
  apply Iso.ext
  exact Iso.inv_hom_id _
lemma associativity (z : Points R c L K b) (w : Points R c K M b)
    (v : Points R c M N b) :
    composition R c L M N b (composition R c L K M b z w) v=
      composition R c L K N b z (composition R c K M N b w v) := by
  apply (ContactWholeIsomPointEquivalence318.equivalence R c L N T b).injective
  simp only [recover_composition]
  apply Iso.ext
  exact Category.assoc _ _ _
end ContactOriginalIsomPointLaws318
