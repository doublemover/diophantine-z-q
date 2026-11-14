module
public import ContactIsomParameterProduct318
public section
noncomputable section
namespace ContactOriginalIsomPointTorsor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomPointOperations318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T : Scheme.{0}} (b : T ⟶ Spec R)
lemma cancel_action (a : Points R c L L b) (z : Points R c L K b) :
    composition R c L K L b (composition R c L L K b a z) (inverse R c L K b z)=a := by
  rw [ContactOriginalIsomPointLaws318.associativity,
    ContactOriginalIsomPointLaws318.left_inverse,ContactOriginalIsomPointLaws318.right_identity]
lemma cancel_difference (z w : Points R c L K b) :
    composition R c L L K b (composition R c L K L b z (inverse R c L K b w)) w=z := by
  rw [ContactOriginalIsomPointLaws318.associativity,
    ContactOriginalIsomPointLaws318.right_inverse,ContactOriginalIsomPointLaws318.right_identity]
/-- Exact simply transitive action on full original Isom points whenever
points exist. It remains an equivalence when both relevant sets are empty;
no global section or local nonemptiness is inserted as a premise. -/
@[expose] def shear : (Points R c L L b × Points R c L K b) ≃
    (Points R c L K b × Points R c L K b) where
  toFun az := (composition R c L L K b az.1 az.2,az.2)
  invFun zw := (composition R c L K L b zw.1 (inverse R c L K b zw.2),zw.2)
  left_inv az := Prod.ext (cancel_action R c L K b az.1 az.2) rfl
  right_inv zw := Prod.ext (cancel_difference R c L K b zw.1 zw.2) rfl
end ContactOriginalIsomPointTorsor318
