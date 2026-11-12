module
public import ContactSectionCoefficientCongr318
public import ContactParameterUnitZeros318
public import ContactUniversalClassifiedZeroParameter318
public section
noncomputable section
namespace ContactClassifiedUnitZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318 ContactUniversalZeroSpecialization318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : A →ₐ[ℚ] S) (u : Sˣ)
local notation "f" => g.comp (parameterCoefficient R c L)
local instance : Algebra R S := f.toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local notation "a" => parameterPoint R c L S g

@[expose] def scaledPoint : A →ₐ[R] S :=
  ProjectiveParameterUnitAction318.pointScale R Γ(L.object,⊤) S (u:S) a
@[expose] def scaledCoefficient : A →ₐ[ℚ] S :=
  (scaledPoint R c L S g u).restrictScalars ℚ
local notation "g'" => scaledCoefficient R c L S g u

/-- Scaling parameters does not change the ACTUAL original coefficient
map. This equality is proved explicitly before comparing pulled lines. -/
lemma coefficient_base : g'.comp (parameterCoefficient R c L)=f := by
  apply AlgHom.ext
  intro r
  exact (scaledPoint R c L S g u).commutes r
lemma point_ring : (scaledPoint R c L S g u).toRingHom=
    (parameterPoint R c L S g').toRingHom := rfl

/-- The actual classified zeros after unit scaling, including the
coefficient-induced line equality rather than a hidden scalar-instance
identification, are isomorphic over the SAME original contact curve. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g')
    (classifiedSection R c L hz S g') ≅
    ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g)
      (classifiedSection R c L hz S g) :=
  ContactSectionCoefficientCongr318.zeroIso R c L hz S f (g'.comp (parameterCoefficient R c L))
    (scaledPoint R c L S g u) (parameterPoint R c L S g')
    (coefficient_base R c L S g u).symm (point_ring R c L S g u) ≪≫
    ContactParameterUnitZeros318.zeroIso R c L hz S f u a

@[reassoc] lemma iso_into : (iso R c L hz S g u).hom ≫
    ContactGlobalSectionZero318.into S c (classifiedLine R c L S g)
      (classifiedSection R c L hz S g)=
    ContactGlobalSectionZero318.into S c (classifiedLine R c L S g')
      (classifiedSection R c L hz S g') := by
  rw [iso,Iso.trans_hom,Category.assoc,ContactParameterUnitZeros318.zeroIso_into,
    ContactSectionCoefficientCongr318.zeroIso_into]
@[reassoc] lemma iso_projection : (iso R c L hz S g u).hom ≫
    ContactGlobalResidueFlat318.projection S c (classifiedLine R c L S g)
      (classifiedSection R c L hz S g)=
    ContactGlobalResidueFlat318.projection S c (classifiedLine R c L S g')
      (classifiedSection R c L hz S g') := by
  rw [ContactGlobalResidueFlat318.projection,← Category.assoc,iso_into]
  rfl
end ContactClassifiedUnitZero318
