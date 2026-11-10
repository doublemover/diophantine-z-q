module
public import ContactZeroParameterAmbient318
public import RestrictedFamilyOriginal318
public import ContactLiteralTripleFamilyRotation318
public section
noncomputable section
namespace ContactNormalizedOriginalCurve318
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

/-- The literal map of each normalized zero chart into the ORIGINAL
contact curve over R, through the SAME universal zero and parameter map. -/
@[expose] def chart (i : Fin F.size) : ContactNormalizedChartZeroFamily318.scheme R c L hz i ⟶
    curve R c :=
  pullback.fst _ _ ≫ pullback.fst π W.ι ≫ ContactUniversalGlobalZero318.into R c L hz ≫
    curveMap R A pc c

variable (S : CommRingCat.{0}) [Algebra ℚ S]
@[reassoc] lemma universal_ambient (g : A →ₐ[ℚ] S) :
    (ContactUniversalClassifiedZeroParameter318.iso R c L hz S g).hom ≫
      pullback.fst _ _ ≫ ContactUniversalGlobalZero318.into R c L hz=
    ContactGlobalSectionZero318.into S c (classifiedLine R c L S g)
      (classifiedSection R c L hz S g) ≫ curveMap A S g c :=
  ContactZeroParameterAmbient318.transported A S g c (universalLine R c L)
    (universalSection R c L hz) (classifiedLine R c L S g)
    (classifiedSection R c L hz S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R A S pc g c L)
    (ContactUniversalGeometricSpecialization318.specialize R c L hz S g)

variable (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
variable (i : Fin F.size) (a : A →ₐ[R] S)
  (ha : a (ProjectiveParameterZeroCoordinates318.coordinate R P i)=1)
local notation "N" => L' R S f c L
local notation "g" => a.restrictScalars ℚ
private lemma coefficient_base : g.comp pc=f := by
  apply AlgHom.ext
  intro r
  exact a.commutes r

/-- The original normalized-point classifier preserves the ORIGINAL
curve map as well as the coefficient projection. This additional square
is what allows across-ring descent arrows to be compared by a genuine
closed immersion, rather than equality of base points alone. -/
@[reassoc] lemma comparison :
    (ContactNormalizedPointZeroFamily318.iso R c L hz S f i a ha).hom ≫
      pullback.fst _ _ ≫ chart R c L hz i=
    ContactGlobalSectionZero318.into S c N (points R c L hz S f a) ≫ curveMap R S f c := by
  simp only [ContactNormalizedPointZeroFamily318.iso,chart,Iso.trans_hom,Iso.symm_hom,
    Category.assoc]
  rw [RestrictedFamilyOriginal.two_inv_assoc,universal_ambient_assoc,
    ContactCoefficientWholeOpens318.composition,coefficient_base]
  rw [← ContactSectionCoefficientCongr318.zeroIso_into R c L hz S f
    (g.comp pc) a (parameterPoint R c L S g) (coefficient_base R c L S f a).symm rfl,
    Iso.inv_hom_id_assoc]
end ContactNormalizedOriginalCurve318
