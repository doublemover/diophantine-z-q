module
public import ContactNormalizedChartZeroIdentification318
public import ContactUniversalRangeCartier318
public import ContactNormalizedGlobalClosedFamily318
public import RestrictedFamilyOriginal318
public import ContactUniversalClassifiedZeroParameter318
public import ContactNormalizedChartZeroFamily318
public section
noncomputable section
namespace ContactNormalizedCartierTest318
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
abbrev ring := ContactNormalizedChartZeroIdentification318.ring R c L hz i
local notation "S" => ring R c L hz i
instance rationalAlgebra : Algebra ℚ S := ContactNormalizedChartZeroIdentification318.rationalAlgebra R c L hz i
instance rationalTower : IsScalarTower ℚ R S := ContactNormalizedChartZeroIdentification318.rationalTower R c L hz i
abbrev coefficient := ContactNormalizedChartZeroIdentification318.coefficient R c L hz i
local notation "g" => coefficient R c L hz i
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "W" => ContactUniversalNonzeroLocus318.locus R c L hz
local notation "j" => ContactNormalizedChartZeroFamily318.parameterMap R c L hz i
lemma factor : j ≫ W.ι=Spec.map (CommRingCat.ofHom g.toRingHom) :=
  ProjectiveParameterSliceNonzero318.intoNonzero_fac R Γ(L.object,⊤) i

local notation "U" => universalLine R c L
local notation "σ" => universalSection R c L hz
abbrev line := ContactUniversalResidueNonzero318.line R c L S g
abbrev section : Γ((line R c L hz i).object,⊤) :=
  ContactUniversalResidueNonzero318.section R c L hz S g
abbrev scheme : Scheme := ContactGlobalSectionZero318.scheme S c
  (line R c L hz i) (section R c L hz i)
abbrev into : scheme R c L hz i ⟶ curve S c := ContactGlobalSectionZero318.into S c
  (line R c L hz i) (section R c L hz i)
abbrev projection : scheme R c L hz i ⟶ Spec S := ContactGlobalResidueFlat318.projection S c
  (line R c L hz i) (section R c L hz i)

lemma image_nonzero (x : Spec S) : Spec.map (CommRingCat.ofHom g.toRingHom) x∈W := by
  rw [← factor R c L hz i,Scheme.Hom.comp_apply]
  exact (j x).property

/-- Cartier charts for the EXACT coefficient-pulled original universal
section on the literal coordinate-one test ring. No residue, positivity,
or nonzero-section premise is left to the caller. -/
lemma regular_charts : OriginalRegularClosedCharts318.Property (into R c L hz i) :=
  ContactUniversalRangeCartier318.regular_charts R c L hz S g (image_nonzero R c L hz i)

@[expose] def iso : scheme R c L hz i ≅ ContactNormalizedChartZeroFamily318.scheme R c L hz i :=
  ContactZeroParameterBaseChange318.iso (CommRingCat.of A) S g c U σ ≪≫
    (RestrictedFamilyPullback318.iso π W.ι j (Spec.map (CommRingCat.ofHom g.toRingHom))
      (factor R c L hz i)).symm
@[reassoc] lemma iso_projection : (iso R c L hz i).hom ≫
    ContactNormalizedChartZeroFamily318.projection R c L hz i=projection R c L hz i := by
  rw [iso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    RestrictedFamilyPullback318.inv_projection,ContactZeroParameterBaseChange318.iso_projection]

/-- The SAME test comparison retains the ORIGINAL curve map, not only
the coefficient projection. This is needed for the actual Cartier
embedding, rather than a merely abstract finite-flat test family. -/
@[reassoc] lemma iso_original : (iso R c L hz i).hom ≫
    ContactNormalizedOriginalCurve318.chart R c L hz i=
    into R c L hz i ≫ ContactRelativeCoefficientChange318.curveMap R S
      (g.comp (parameterCoefficient R c L)) c := by
  simp only [iso,ContactNormalizedOriginalCurve318.chart,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [RestrictedFamilyOriginal318.one_inv_assoc,ContactZeroParameterAmbient318.ambient_assoc,
    ContactCoefficientWholeOpens318.composition]
end ContactNormalizedCartierTest318
