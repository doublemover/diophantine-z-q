module
public import ProjectiveParameterNonzeroOpen318
public import ContactUniversalGeometricSpecialization318
public section
noncomputable section
namespace ContactUniversalNonzeroLocus318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

/-- The explicit nonzero-section open of the actual original parameter
scheme. It removes the zero specialization rather than silently asserting
that a total Cartier family is Cartier on all of its fibers. -/
@[expose] def locus : (parameterScheme R c L).Opens :=
  ProjectiveParameterNonzeroOpen318.locus R Γ(L.object,⊤)

variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K]
  (g : parameterRing R c L →ₐ[ℚ] K)
local instance : Algebra R K := (g.comp (parameterCoefficient R c L)).toAlgebra

lemma classified_nonzero_iff :
    ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) K
      (parameterPoint R c L K g) ∈ locus R c L hz ↔
    points R c L hz K (g.comp (parameterCoefficient R c L)) (parameterPoint R c L K g)≠0 := by
  rw [locus,ProjectiveParameterNonzeroOpen318.fieldPoint_mem_iff]
  have hzero : points R c L hz K (g.comp (parameterCoefficient R c L))
      (parameterPoint R c L K g)=0 ↔
      ProjectiveSectionParameter318.points R Γ(L.object,⊤) K (parameterPoint R c L K g)=0 :=
    by
      change (ContactRelativeHZeroBaseChange318.equivalence R K
        (g.comp (parameterCoefficient R c L)) c L hz)
        (ProjectiveSectionParameter318.points R Γ(L.object,⊤) K (parameterPoint R c L K g))=0 ↔ _
      exact (ContactRelativeHZeroBaseChange318.equivalence R K
        (g.comp (parameterCoefficient R c L)) c L hz).map_eq_zero_iff
  exact (not_congr hzero).symm

/-- The SAME geometrically pulled global universal section, with the
original associator, is nonzero exactly on this explicit parameter open. -/
theorem geometric_nonzero_iff :
    ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) K
      (parameterPoint R c L K g) ∈ locus R c L hz ↔
    ContactHZeroCoefficientFunctor318.compositionSections R
      (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L K g
      (OriginalSectionPullbackComposition318.pull
        (ContactRelativeCoefficientChange318.curveMap
          (CommRingCat.of (parameterRing R c L)) K g c) (universalLine R c L).object
        (universalSection R c L hz))≠0 := by
  rw [ContactUniversalGeometricSpecialization318.specialize]
  exact classified_nonzero_iff R c L hz K g
end ContactUniversalNonzeroLocus318
