module
public import ContactArbitraryNowhereZeroOpen318
public import ContactGlobalZeroEmptyIdeals318
public section
noncomputable section
namespace ContactArbitraryNowhereZeroPoints318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
open ContactArbitraryZeroSpecialization318 ContactArbitraryNowhereZeroOpen318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)
local instance : Algebra R S := (g.comp (parameterCoefficient R c L)).toAlgebra

/-- The actual coefficient point factors through the open exactly when
its geometrically specialized section has EMPTY entire zero scheme. -/
lemma factor_iff_empty :
    (∃ h : Spec S ⟶ scheme R c L,
      h ≫ into R c L=Spec.map (CommRingCat.ofHom g.toRingHom)) ↔
    IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g)
      (classifiedSection R c L S g)) :=
  (factor_iff R c L _).trans (empty_iff R c L S g).symm

/-- Full ideal criterion for the genuine open of nowhere-zero sections.
The equivalence holds on arbitrary coefficient rings, including nilpotents. -/
lemma factor_iff_ideals :
    (∃ h : Spec S ⟶ scheme R c L,
      h ≫ into R c L=Spec.map (CommRingCat.ofHom g.toRingHom)) ↔
    ContactOriginalSectionZeros318.finiteIdeal S c (classifiedLine R c L S g)
      (classifiedSection R c L S g)=⊤ ∧
    ContactOriginalSectionZeros318.infinityIdeal S c (classifiedLine R c L S g)
      (classifiedSection R c L S g)=⊤ :=
  (factor_iff_empty R c L S g).trans (ContactGlobalZeroEmptyIdeals318.iff_top S c _ _)
end ContactArbitraryNowhereZeroPoints318
