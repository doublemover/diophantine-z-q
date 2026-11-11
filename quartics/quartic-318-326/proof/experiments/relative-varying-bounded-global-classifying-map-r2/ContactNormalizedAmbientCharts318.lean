module
public import ContactNormalizedCartierTest318
public import RelativeAmbientCharts318
public import ContactUniversalRangeCartier318
public import ContactNormalizedGlobalClosedFamily318
public import RestrictedFamilyOriginal318
public import ContactUniversalClassifiedZeroParameter318
public import ContactNormalizedChartZeroFamily318
public section
noncomputable section
namespace ContactNormalizedAmbientCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (i : Fin F.size)
local notation "S" => ContactNormalizedCartierTest318.ring R c L hz i
local notation "g" => ContactNormalizedCartierTest318.coefficient R c L hz i
local notation "f" => g.comp (parameterCoefficient R c L)
local notation "B" => ContactNormalizedSectionParameter318.scheme R c L hz
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "u" => ProjectiveParameterSliceGluing318.into R Γ(L.object,⊤) i
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "a" => ContactRelativeCoefficientChange318.curveMap R S f c
local notation "d" => ContactRelativeStructuralHOne318.projection S c
lemma base_spec : Spec.map (CommRingCat.ofHom f.toRingHom)=
    ProjectiveParameterSliceSchemes318.projection R Γ(L.object,⊤) i := by
  rw [ProjectiveParameterSliceSchemes318.projection]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Ideal.Quotient.mkₐ R
    (ProjectiveParameterSliceAlgebra318.ideal R Γ(L.object,⊤) i)).commutes r

lemma coefficient_square : IsPullback a d q (u ≫ b) := by
  change IsPullback a d q (u ≫ ProjectiveParameterSliceBase318.projection R Γ(L.object,⊤))
  rw [ProjectiveParameterSliceBase318.into_projection,← base_spec R c L hz i]
  exact ContactZeroParameterBaseChange318.ambient_square R S f c

/-- The ambient chart is the ORIGINAL contact model over the SAME
literal coordinate-one ring, not an abstract chart with matching points. -/
@[expose] def into : curve S c ⟶ ContactNormalizedGlobalClosedFamily318.ambient R c L hz :=
  RelativeAmbientCharts318.lift q b u a d (coefficient_square R c L hz i)
@[reassoc] lemma into_original : into R c L hz i ≫ pullback.fst q b=a :=
  RelativeAmbientCharts318.lift_original ..
@[reassoc] lemma into_projection : into R c L hz i ≫ pullback.snd q b=d ≫ u :=
  RelativeAmbientCharts318.lift_projection ..
lemma square : IsPullback (into R c L hz i) d
    (ContactNormalizedGlobalClosedFamily318.ambientProjection R c L hz) u :=
  RelativeAmbientCharts318.square ..
instance openImmersion : IsOpenImmersion (into R c L hz i) := inferInstanceAs
  (IsOpenImmersion (RelativeAmbientCharts318.lift q b u a d (coefficient_square R c L hz i)))
end ContactNormalizedAmbientCharts318
