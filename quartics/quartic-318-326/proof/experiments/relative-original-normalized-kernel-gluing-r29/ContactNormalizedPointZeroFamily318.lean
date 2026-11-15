module
public import ContactNormalizedZeroTransitions318
public section
noncomputable section
namespace ContactNormalizedPointZeroFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactCoefficientNativeSections318 ContactUniversalGeometricSpecialization318
open ContactUniversalZeroSpecialization318
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
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
variable (i : Fin F.size) (a : A →ₐ[R] S)
  (ha : a (ProjectiveParameterZeroCoordinates318.coordinate R P i)=1)
local notation "N" => L' R S f c L
local notation "g" => a.restrictScalars ℚ
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "m" => ContactNormalizedChartZeroFamily318.parameterMap R c L hz i

@[expose] def sliceMap : ProjectiveParameterSliceAlgebra318.algebra R P i →ₐ[R] S :=
  (ProjectiveParameterSliceAlgebra318.points R P i S).symm ⟨a,ha⟩
lemma sliceMap_mk (z : A) : sliceMap R c L hz S f i a ha
    (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) z)=a z :=
  DFunLike.congr_fun (congrArg Subtype.val
    ((ProjectiveParameterSliceAlgebra318.points R P i S).apply_symm_apply ⟨a,ha⟩)) z
@[expose] def testMap : Spec S ⟶ ProjectiveParameterSliceSchemes318.chart R P i :=
  Spec.map (CommRingCat.ofHom (sliceMap R c L hz S f i a ha).toRingHom)
lemma parameter_factor : testMap R c L hz S f i a ha ≫ m ≫ W.ι=
    Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [ContactNormalizedChartZeroIdentification318.factor,testMap,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact sliceMap_mk R c L hz S f i a ha

private lemma coefficient_base : g.comp (parameterCoefficient R c L)=f := by
  apply AlgHom.ext
  intro r
  exact a.commutes r

/-- The actual normalized point classifies a section of the ORIGINAL
fixed coefficient pullback line. Its zero scheme is the actual pullback
of the original finite-flat normalized chart family, including the
coefficient-line transport and both Cartesian restriction comparisons. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c N (points R c L hz S f a) ≅
    pullback (ContactNormalizedChartZeroFamily318.projection R c L hz i)
      (testMap R c L hz S f i a ha) :=
  (ContactSectionCoefficientCongr318.zeroIso R c L hz S f
    (g.comp (parameterCoefficient R c L)) a (parameterPoint R c L S g)
    (coefficient_base R c L S f a).symm rfl).symm ≪≫
  ContactUniversalClassifiedZeroParameter318.iso R c L hz S g ≪≫
  (TwoRestrictedFamilyPullback318.iso π W.ι m (testMap R c L hz S f i a ha)
    (Spec.map (CommRingCat.ofHom g.toRingHom))
    (parameter_factor R c L hz S f i a ha)).symm

@[reassoc] lemma iso_projection : (iso R c L hz S f i a ha).hom ≫ pullback.snd _ _=
    ContactGlobalResidueFlat318.projection S c N (points R c L hz S f a) := by
  rw [iso,Iso.trans_hom,Iso.trans_hom,Iso.symm_hom,Category.assoc,Category.assoc,
    TwoRestrictedFamilyPullback318.inv_projection,
    ContactUniversalClassifiedZeroParameter318.iso_projection]
  change _ ≫ (ContactGlobalSectionZero318.into S c (classifiedLine R c L S g)
    (classifiedSection R c L hz S g) ≫ ContactRelativeStructuralHOne318.projection S c)=_
  rw [← ContactSectionCoefficientCongr318.zeroIso_into R c L hz S f
    (g.comp (parameterCoefficient R c L)) a (parameterPoint R c L S g)
    (coefficient_base R c L S f a).symm rfl,
    Iso.inv_hom_id_assoc]
  rfl
end ContactNormalizedPointZeroFamily318
