module
public import ContactArbitraryUniversalZero318
public import ContactZeroTransportedParameter318
public section
noncomputable section
namespace ContactArbitraryZeroSpecialization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318 ContactArbitraryUniversalZero318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)
local instance : Algebra R S := (g.comp (parameterCoefficient R c L)).toAlgebra
abbrev classifiedLine := L' R S (g.comp (parameterCoefficient R c L)) c L
abbrev classifiedSection : Γ((classifiedLine R c L S g).object,⊤) :=
  ContactArbitrarySectionParameter318.points R c L S (g.comp (parameterCoefficient R c L))
    (ContactHZeroCoefficientFunctor318.coefficientArrow R (CommRingCat.of (parameterRing R c L))
      (parameterCoefficient R c L) S g)

/-- The classified zero scheme is the genuine parameter-basechange of the same
universal zero family, consuming actual geometric universal-section specialization. -/
@[expose] def iso :
    ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g) (classifiedSection R c L S g) ≅
    pullback (projection R c L) (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
  ContactZeroTransportedParameter318.iso (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L)
    (classifiedLine R c L S g) (classifiedSection R c L S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactArbitraryUniversalSection318.specialize R c L S g)

@[reassoc] lemma iso_projection : (iso R c L S g).hom ≫ pullback.snd _ _ =
    ContactGlobalResidueFlat318.projection S c (classifiedLine R c L S g) (classifiedSection R c L S g) :=
  ContactZeroTransportedParameter318.iso_projection (CommRingCat.of (parameterRing R c L)) S g c
    (universalLine R c L) (universalSection R c L)
    (classifiedLine R c L S g) (classifiedSection R c L S g)
    (ContactDerivedCoefficientFunctor318.compositionIso R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L)
    (ContactArbitraryUniversalSection318.specialize R c L S g)

lemma empty_iff :
    IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (classifiedLine R c L S g)
      (classifiedSection R c L S g)) ↔
    IsEmpty ↑(pullback (projection R c L) (Spec.map (CommRingCat.ofHom g.toRingHom))) := by
  constructor
  · intro h
    exact ⟨fun z => h.false ((iso R c L S g).inv z)⟩
  · intro h
    exact ⟨fun z => h.false ((iso R c L S g).hom z)⟩
end ContactArbitraryZeroSpecialization318
