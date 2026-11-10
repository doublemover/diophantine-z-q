module
public import ContactZeroTransportedBaseChange318
public import ContactUniversalGeometricSpecialization318
public section
noncomputable section
namespace ContactUniversalZeroSpecialization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)
local instance : Algebra R S := (g.comp (parameterCoefficient R c L)).toAlgebra

abbrev classifiedLine := L' R S (g.comp (parameterCoefficient R c L)) c L
abbrev classifiedSection : Γ((classifiedLine R c L S g).object,⊤) :=
  points R c L hz S (g.comp (parameterCoefficient R c L)) (parameterPoint R c L S g)

/-- The zero scheme of the CLASSIFIED original section is the actual
geometric base change of the SAME universal zero closed subscheme.
Both the original line associator and its section-specialization identity
are constructed and consumed here; this is not a fiber cardinality claim. -/
@[expose] def iso :
    ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g) (classifiedSection R c L hz S g) ≅
    pullback (ContactRelativeCoefficientChange318.curveMap (CommRingCat.of (parameterRing R c L)) S g c)
      (ContactUniversalGlobalZero318.into R c L hz) :=
  ContactZeroTransportedBaseChange318.iso (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L hz)
    (classifiedLine R c L S g) (classifiedSection R c L hz S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactUniversalGeometricSpecialization318.specialize R c L hz S g)

@[reassoc] lemma iso_fst : (iso R c L hz S g).hom ≫ pullback.fst _ _ =
    ContactGlobalSectionZero318.into S c (classifiedLine R c L S g) (classifiedSection R c L hz S g) :=
  ContactZeroTransportedBaseChange318.iso_fst (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L hz)
    (classifiedLine R c L S g) (classifiedSection R c L hz S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactUniversalGeometricSpecialization318.specialize R c L hz S g)
end ContactUniversalZeroSpecialization318
