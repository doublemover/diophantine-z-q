module
public import ContactNormalizedGlobalJointMono318
public import ContactNormalizedGlobalDegree318
public import RestrictedFamilyOriginal318
public import ContactLiteralTripleFamilyRotation318
public section
noncomputable section
namespace ContactNormalizedGlobalRelative318
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

/-- The literal coordinate-one chart has the same coefficient base map
through its actual factorization into the nonzero parameter open. -/
@[reassoc] lemma parameter_base (i : Fin F.size) :
    ContactNormalizedChartZeroFamily318.parameterMap R c L hz i ≫ W.ι ≫
      Spec.map (CommRingCat.ofHom pc.toRingHom)=
        ProjectiveParameterSliceSchemes318.projection R P i := by
  rw [ContactNormalizedChartZeroFamily318.parameterMap,← Category.assoc,
    ProjectiveParameterSliceNonzero318.intoNonzero_fac,
    ProjectiveParameterSliceNonzero318.parameterMap,
    ProjectiveParameterSliceSchemes318.projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P i)).commutes r

@[reassoc] lemma universal_relative : ContactUniversalGlobalZero318.into R c L hz ≫
    curveMap R A pc c ≫ ContactRelativeStructuralHOne318.projection R c=
      π ≫ Spec.map (CommRingCat.ofHom pc.toRingHom) := by
  rw [(ContactZeroParameterBaseChange318.ambient_square R A pc c).w,← Category.assoc]
  rfl

/-- Each original normalized chart map lies over precisely its original
coefficient morphism. This retains the actual structural map of the curve. -/
@[reassoc] lemma chart_relative (i : Fin F.size) :
    ContactNormalizedOriginalCurve318.chart R c L hz i ≫
      ContactRelativeStructuralHOne318.projection R c=
    ContactNormalizedChartZeroFamily318.projection R c L hz i ≫
      ProjectiveParameterSliceSchemes318.projection R P i := by
  rw [ContactNormalizedOriginalCurve318.chart]
  simp only [Category.assoc]
  rw [universal_relative]
  rw [← Category.assoc (pullback.fst π W.ι),pullback.condition]
  rw [Category.assoc,← Category.assoc (pullback.fst _ _),pullback.condition]
  rw [Category.assoc,parameter_base]

/-- The genuinely glued zero family and original curve map form a
commutative square over the ORIGINAL coefficient base, proved on the
full actual zero open cover. -/
lemma square : ContactNormalizedGlobalOriginal318.original R c L hz ≫
    ContactRelativeStructuralHOne318.projection R c=
      ContactNormalizedZeroProjection318.projection R c L hz ≫
        ContactNormalizedSectionParameter318.projection R c L hz := by
  apply (ContactNormalizedGlobalZero318.cover R c L hz).hom_ext
  intro i
  change ContactNormalizedGlobalZero318.into R c L hz i ≫ _ =
    ContactNormalizedGlobalZero318.into R c L hz i ≫ _
  rw [← Category.assoc,ContactNormalizedGlobalOriginal318.into_original,
    ← Category.assoc,ContactNormalizedZeroProjection318.into_projection,Category.assoc]
  change ContactNormalizedOriginalCurve318.chart R c L hz i ≫
    ContactRelativeStructuralHOne318.projection R c=
      ContactNormalizedChartZeroFamily318.projection R c L hz i ≫
        ProjectiveParameterSliceGluing318.into R P i ≫ ProjectiveParameterSliceBase318.projection R P
  rw [ProjectiveParameterSliceBase318.into_projection,chart_relative]
end ContactNormalizedGlobalRelative318
