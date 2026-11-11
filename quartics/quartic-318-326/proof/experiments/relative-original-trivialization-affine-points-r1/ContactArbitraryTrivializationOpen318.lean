module
public import ContactZeroEmptyTrivialization318
public import ContactArbitraryNowhereZeroPoints318
public section
noncomputable section
namespace ContactArbitraryTrivializationOpen318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
open ContactArbitraryZeroSpecialization318 ContactArbitraryNowhereZeroOpen318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)
local instance : Algebra R S := (g.comp (parameterCoefficient R c L)).toAlgebra

/-- The previously constructed honest open is now identified with the
invertibility of the SAME classified O-linear map, not just a support test. -/
lemma factor_iff_isIso :
    (∃ h : Spec S ⟶ scheme R c L,
      h ≫ into R c L=Spec.map (CommRingCat.ofHom g.toRingHom)) ↔
    IsIso (ModuleGlobalSections318.ofTop (classifiedLine R c L S g).object
      (classifiedSection R c L S g)) :=
  (ContactArbitraryNowhereZeroPoints318.factor_iff_empty R c L S g).trans
    (ContactZeroEmptyTrivialization318.empty_iff_isIso S c _ _)

/-- A point in the actual open produces the actual full sheaf
trivialization of its literal classified original line. -/
@[expose] def frame (h : Spec S ⟶ scheme R c L)
    (hh : h ≫ into R c L=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    SheafOfModules.unit (curve S c).ringCatSheaf ≅ (classifiedLine R c L S g).object := by
  letI := (factor_iff_isIso R c L S g).mp ⟨h,hh⟩
  exact asIso (ModuleGlobalSections318.ofTop (classifiedLine R c L S g).object
    (classifiedSection R c L S g))

lemma frame_value (h : Spec S ⟶ scheme R c L)
    (hh : h ≫ into R c L=Spec.map (CommRingCat.ofHom g.toRingHom)) :
    (frame R c L S g h hh).hom.app ⊤ 1=classifiedSection R c L S g :=
  ModuleTopMorphisms318.ofTop_top_one _
end ContactArbitraryTrivializationOpen318
