module
public import OriginalAutomorphismScalarPullback318
public section
noncomputable section
namespace ContactOriginalBaseUnitAutomorphisms318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "q" => ContactCanonicalCoefficientFrame318.projection R c
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
/-- The full original stabilizer is now classified by actual BASE
units on every whole scheme test, not by an assumed constants theorem. -/
@[expose] def equivalence : Points R c L L b ≃ Γ(T,⊤)ˣ :=
  (ContactOriginalAutomorphismCommutativity318.values R c L b).trans
    (ContactOriginalNestedFunctionConstants318.units R c b).symm.toEquiv
lemma recover (z : Points R c L L b) :
    ContactOriginalNestedFunctionConstants318.units R c b (equivalence R c L b z)=
      ContactOriginalAutomorphismCommutativity318.values R c L b z :=
  (ContactOriginalNestedFunctionConstants318.units R c b).apply_symm_apply _
lemma classify (a : Γ(T,⊤)ˣ) :
    ContactOriginalAutomorphismCommutativity318.values R c L b ((equivalence R c L b).symm a)=
      ContactOriginalNestedFunctionConstants318.units R c b a :=
  (ContactOriginalAutomorphismCommutativity318.values R c L b).apply_symm_apply _
lemma multiplication (z w : Points R c L L b) :
    equivalence R c L b (ContactOriginalIsomPointOperations318.composition R c L L L b z w)=
      equivalence R c L b z*equivalence R c L b w := by
  apply (ContactOriginalNestedFunctionConstants318.units R c b).injective
  rw [map_mul,recover,recover,recover]
  change OriginalLineAutomorphismUnits318.value _
    (ContactWholeIsomPointEquivalence318.equivalence R c L L T b
      (ContactOriginalIsomPointOperations318.composition R c L L L b z w))=_
  rw [ContactOriginalIsomPointOperations318.recover_composition,
    OriginalLineAutomorphismUnits318.value_multiplication]
end ContactOriginalBaseUnitAutomorphisms318
