module
public import ContactOriginalBaseUnitAutomorphisms318
public section
noncomputable section
namespace ContactOriginalBaseUnitNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "q" => ContactCanonicalCoefficientFrame318.projection R c
variable {T T' : Scheme.{0}} (b : T ⟶ Spec R) (b' : T' ⟶ Spec R)
  (h : T' ⟶ T) (hh : h ≫ b=b')
lemma family_values (z : Points R c L L b) :
    ContactOriginalAutomorphismCommutativity318.values R c L b'
      (pointMap R c L L b b' h hh z)=
    Units.map (RelativeSchemeCoefficient318.map q b b' h hh).appTop.hom.toMonoidHom
      (ContactOriginalAutomorphismCommutativity318.values R c L b z) := by
  change OriginalLineAutomorphismUnits318.value _
    (ContactWholeIsomPointEquivalence318.equivalence R c L L T' b' (pointMap R c L L b b' h hh z))=_
  rw [←ContactWholeIsomNaturality318.recovery]
  exact OriginalAutomorphismScalarPullback318.path_value _ _ _ _ L _
/-- Full original automorphisms and base units have the SAME native
restriction action on all whole tests, with no affine or flat premise. -/
lemma natural (z : Points R c L L b) :
    ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b'
      (pointMap R c L L b b' h hh z)=
    Units.map h.appTop.hom.toMonoidHom
      (ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b z) := by
  apply (ContactOriginalNestedFunctionConstants318.units R c b').injective
  rw [ContactOriginalBaseUnitAutomorphisms318.recover,
    ←ContactOriginalNestedFunctionConstants318.units_natural R c b b' h hh,
    ContactOriginalBaseUnitAutomorphisms318.recover]
  exact family_values R c L b b' h hh z
lemma classify_natural (a : Γ(T,⊤)ˣ) :
    pointMap R c L L b b' h hh ((ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b).symm a)=
    (ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b').symm
      (Units.map h.appTop.hom.toMonoidHom a) := by
  apply (ContactOriginalBaseUnitAutomorphisms318.equivalence R c L b').injective
  rw [natural,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
end ContactOriginalBaseUnitNaturality318
