module
public import CoveredFamilyJointMono318
public import ContactNormalizedGlobalDegree318
public import RestrictedFamilyOriginal318
public import ContactLiteralTripleFamilyRotation318
public section
noncomputable section
namespace ContactNormalizedChartJointMono318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactCoefficientNativeSections318 ContactUniversalGeometricSpecialization318
open ContactUniversalZeroSpecialization318 ContactRelativeCoefficientChange318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "pc" => parameterCoefficient R c L

/-- The original universal zero embedding and actual coefficient
Cartesian square give joint monicity of old-curve and parameter maps. -/
lemma universal {X : Scheme} (v w : X ⟶ ContactUniversalGlobalZero318.scheme R c L hz)
    (hc : v ≫ ContactUniversalGlobalZero318.into R c L hz ≫ curveMap R A pc c=
      w ≫ ContactUniversalGlobalZero318.into R c L hz ≫ curveMap R A pc c)
    (hp : v ≫ π=w ≫ π) : v=w := by
  apply (cancel_mono (ContactUniversalGlobalZero318.into R c L hz)).1
  apply (ContactZeroParameterBaseChange318.ambient_square R A pc c).hom_ext
  · simpa only [Category.assoc] using hc
  · simpa only [ContactUniversalGlobalZero318.projection,Category.assoc] using hp

/-- BOTH actual restrictions preserve the old-curve/base joint monicity:
first the nonzero open, then the actual normalized coefficient-one slice. -/
lemma hom_ext (i : Fin F.size) {X : Scheme}
    (v w : X ⟶ ContactNormalizedChartZeroFamily318.scheme R c L hz i)
    (hc : v ≫ ContactNormalizedOriginalCurve318.chart R c L hz i=
      w ≫ ContactNormalizedOriginalCurve318.chart R c L hz i)
    (hp : v ≫ ContactNormalizedChartZeroFamily318.projection R c L hz i=
      w ≫ ContactNormalizedChartZeroFamily318.projection R c L hz i) : v=w := by
  apply CoveredFamilyJointMono318.restrict
    (pullback.fst π W.ι ≫ ContactUniversalGlobalZero318.into R c L hz ≫ curveMap R A pc c)
    (ContactUniversalNonzeroFamily318.projection R c L hz)
    (fun u v hu hv => CoveredFamilyJointMono318.restrict
      (ContactUniversalGlobalZero318.into R c L hz ≫ curveMap R A pc c) π
      (universal R c L hz) W.ι u v hu hv)
    (ContactNormalizedChartZeroFamily318.parameterMap R c L hz i) v w
  · simpa only [ContactNormalizedOriginalCurve318.chart,Category.assoc] using hc
  · exact hp
end ContactNormalizedChartJointMono318
