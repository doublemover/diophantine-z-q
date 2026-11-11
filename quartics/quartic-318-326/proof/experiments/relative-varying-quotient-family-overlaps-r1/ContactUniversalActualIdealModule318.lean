module
public import ActualClosedIdealModule318
public import ContactUniversalCartierCharts318
public section
noncomputable section
namespace ContactUniversalActualIdealModule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactGeneratedLocalUniversalRegular318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "M" => generatedLine R c L
local instance : Module R Γ(M.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) M ⊤
local notation "S" => CommRingCat.of (parameterRing R c M)
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
local notation "U" => universalLine R c M
local notation "s" => universalSection R c M (properties R c L).1
local notation "p" => ContactGlobalSectionZero318.into S c U s

/-- The actual module sheaf of the SAME original universal zero ideal,
constructed as kernel of O→p_*O_zero. It is not a relabeling of the
IdealSheafData record as an O-module. -/
@[expose] def object : (curve S c).Modules := ActualClosedIdealModule318.object p
@[expose] def inclusion : object R c L ⟶ SheafOfModules.unit (curve S c).ringCatSheaf :=
  ActualClosedIdealModule318.inclusion p
instance : Mono (inclusion R c L) := inferInstance

@[reassoc] lemma inclusion_structure : inclusion R c L ≫ ActualClosedIdealModule318.structure p=0 :=
  ActualClosedIdealModule318.inclusion_structure p

/-- The actual module kernel has EXACTLY the previously constructed
original global zero ideal data on every affine open, retaining nilpotents
and the original closed immersion. -/
lemma affine_kernel (V : (curve S c).affineOpens) :
    LinearMap.ker ((SheafOfModules.evaluation (curve S c).ringCatSheaf (op V.1)).map
      (ActualClosedIdealModule318.structure p)).hom =
      (ContactGlobalZeroClosed318.idealSheaf S c U s).ideal V :=
  ActualClosedIdealModule318.section_kernel_idealData p V

/-- Existing canonical kernel-section isomorphism also retains the
literal inclusion into the original structure sheaf on every open. -/
@[expose] def sectionsIso (V : (curve S c).Opens) := ActualClosedIdealModule318.sectionsIso p V
end ContactUniversalActualIdealModule318
