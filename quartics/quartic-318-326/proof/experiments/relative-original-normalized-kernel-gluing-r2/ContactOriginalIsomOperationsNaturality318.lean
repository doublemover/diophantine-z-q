module
public import ContactOriginalIsomPointLaws318
public section
noncomputable section
namespace ContactOriginalIsomOperationsNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
open ContactOriginalIsomPointOperations318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M : Line (curve R c)) {T T' : Scheme.{0}}
  (b : T ⟶ Spec R) (b' : T' ⟶ Spec R) (h : T' ⟶ T) (hh : h ≫ b=b')
lemma identity :
    pointMap R c L L b b' h hh (ContactOriginalIsomPointOperations318.identity R c L b)=
      ContactOriginalIsomPointOperations318.identity R c L b' := by
  unfold ContactOriginalIsomPointOperations318.identity
  rw [←ContactWholeIsomNaturality318.classify]
  congr 1
  exact OriginalNativeIsomPullback318.identity _ _ _ _ _
lemma inverse (z : Points R c L K b) :
    pointMap R c K L b b' h hh (ContactOriginalIsomPointOperations318.inverse R c L K b z)=
      ContactOriginalIsomPointOperations318.inverse R c L K b'
        (pointMap R c L K b b' h hh z) := by
  unfold ContactOriginalIsomPointOperations318.inverse
  rw [←ContactWholeIsomNaturality318.classify,←ContactWholeIsomNaturality318.recovery]
  congr 1
  exact OriginalNativeIsomPullback318.inverse _ _ _ _ _ _ _
lemma composition (z : Points R c L K b) (w : Points R c K M b) :
    pointMap R c L M b b' h hh (ContactOriginalIsomPointOperations318.composition R c L K M b z w)=
      ContactOriginalIsomPointOperations318.composition R c L K M b'
        (pointMap R c L K b b' h hh z) (pointMap R c K M b b' h hh w) := by
  unfold ContactOriginalIsomPointOperations318.composition
  rw [←ContactWholeIsomNaturality318.classify,←ContactWholeIsomNaturality318.recovery,
    ←ContactWholeIsomNaturality318.recovery]
  congr 1
  exact OriginalNativeIsomPullback318.composition _ _ _ _ _ _ _ _ _
end ContactOriginalIsomOperationsNaturality318
