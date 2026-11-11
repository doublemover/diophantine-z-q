module
public import ContactHZeroCoefficientFunctor318
public import ContactUniversalZeroFinitePresentation318
public section
noncomputable section
namespace ContactUniversalGeometricSpecialization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)
local instance : Algebra R S := (g.comp (parameterCoefficient R c L)).toAlgebra

/-- A point of the actual section parameter scheme determines the
coefficient test by its actual composition with the structural R map.
This is the same R-algebra point consumed by the section classifier. -/
@[expose] def parameterPoint : parameterRing R c L →ₐ[R] S :=
  ContactHZeroCoefficientFunctor318.coefficientArrow R (CommRingCat.of (parameterRing R c L))
    (parameterCoefficient R c L) S g

/-- Geometrically pull back the SAME universal GLOBAL section along the
actual parameter map, then the ORIGINAL pullback associator identifies it
with the classified original section. This closes the previous tensor-only
specialization boundary; no newly selected section is substituted. -/
lemma specialize :
    ContactHZeroCoefficientFunctor318.compositionSections R
      (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L S g
      (pull (ContactRelativeCoefficientChange318.curveMap
          (CommRingCat.of (parameterRing R c L)) S g c) (universalLine R c L).object
        (universalSection R c L hz)) =
    points R c L hz S (g.comp (parameterCoefficient R c L)) (parameterPoint R c L S g) := by
  have h := ContactHZeroCoefficientFunctor318.specialize R
    (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L S g hz
    (ProjectiveSectionParameter318.universal R Γ(L.object,⊤))
  change _ = ContactRelativeHZeroBaseChange318.equivalence R S
    (g.comp (parameterCoefficient R c L)) c L hz
    (ProjectiveSectionParameter318.transport R Γ(L.object,⊤) (parameterRing R c L)
      (parameterPoint R c L S g) (ProjectiveSectionParameter318.universal R Γ(L.object,⊤))) at h
  rw [h]
  exact ContactOriginalSectionParameter318.specialize R c L hz S
    (g.comp (parameterCoefficient R c L)) (parameterPoint R c L S g)
end ContactUniversalGeometricSpecialization318
