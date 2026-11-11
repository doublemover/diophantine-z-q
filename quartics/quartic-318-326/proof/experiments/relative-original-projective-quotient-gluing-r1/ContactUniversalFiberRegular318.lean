module
public import ContactFieldIntegralLine318
public import ContactUniversalNonzeroLocus318
public section
noncomputable section
namespace ContactUniversalFiberRegular318
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
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K]
  (g : parameterRing R c L →ₐ[ℚ] K)
local instance : Algebra R K := (g.comp (parameterCoefficient R c L)).toAlgebra
local notation "N" => ContactCoefficientNativeSections318.L' R K
  (g.comp (parameterCoefficient R c L)) c L

/-- The literal geometrically pulled universal section, expressed in the
original coefficient line by its ORIGINAL associator. -/
abbrev section : Γ(N.object,⊤) :=
  ContactHZeroCoefficientFunctor318.compositionSections R
    (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L K g
    (OriginalSectionPullbackComposition318.pull
      (ContactRelativeCoefficientChange318.curveMap
        (CommRingCat.of (parameterRing R c L)) K g c) (universalLine R c L).object
      (universalSection R c L hz))

/-- Every field-valued point of the explicit nonzero-section open has a
regular SAME universal section on every nonempty actual original line
frame. The missing integral-source input is supplied by the proved
geometric integrality of the actual contact model, not assumed. -/
theorem frame_regular
    (hg : ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) K
      (parameterPoint R c L K g) ∈ ContactUniversalNonzeroLocus318.locus R c L hz)
    (V : (curve K c).Opens) [Nonempty V]
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ N.object.restrict V.ι)
    (a : Γ(curve K c,V))
    (ha : a * (OpenLineFrameCoordinates318.frame N.object V e V le_rfl).symm
      (N.object.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (section R c L hz K g))=0) : a=0 := by
  have hn : section R c L hz K g≠0 :=
    (ContactUniversalNonzeroLocus318.geometric_nonzero_iff R c L hz K g).mp hg
  exact ContactFieldIntegralLine318.frame_regular K c N (section R c L hz K g) hn V e a ha
end ContactUniversalFiberRegular318
