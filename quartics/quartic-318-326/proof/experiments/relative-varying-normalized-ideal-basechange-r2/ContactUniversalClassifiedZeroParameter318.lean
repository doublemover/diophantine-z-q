module
public import ContactZeroTransportedParameter318
public import ContactUniversalZeroSpecialization318
public section
noncomputable section
namespace ContactUniversalClassifiedZeroParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalZeroSpecialization318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)

/-- The original classified section-zero scheme is the actual pullback
of the original universal ZERO PROJECTION, not only its ambient embedding. -/
@[expose] def iso : ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g)
    (classifiedSection R c L hz S g) ≅
    pullback (ContactUniversalGlobalZero318.projection R c L hz)
      (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
  ContactZeroTransportedParameter318.iso (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L hz)
    (classifiedLine R c L S g) (classifiedSection R c L hz S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactUniversalGeometricSpecialization318.specialize R c L hz S g)

@[reassoc] lemma iso_projection : (iso R c L hz S g).hom ≫ pullback.snd _ _=
    ContactGlobalResidueFlat318.projection S c (classifiedLine R c L S g)
      (classifiedSection R c L hz S g) :=
  ContactZeroTransportedParameter318.iso_projection (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L hz)
    (classifiedLine R c L S g) (classifiedSection R c L hz S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactUniversalGeometricSpecialization318.specialize R c L hz S g)
end ContactUniversalClassifiedZeroParameter318
