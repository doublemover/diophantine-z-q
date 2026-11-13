module
public import ContactArbitraryCoefficientCongrRebuild318
public import ContactArbitraryNowhereZeroOpen318
public section
noncomputable section
namespace ContactArbitraryAffineNowhereZeroRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
/-- Actual affine coefficient tests use the specified f-action; the
classified line for the rational underlying parameter is compared explicitly. -/
lemma factor_iff_empty :
    letI : Algebra R S := f.toAlgebra
    ∀ a : parameterRing R c L →ₐ[R] S,
      (∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L =
          Spec.map (CommRingCat.ofHom a.toRingHom)) ↔
      IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (L' R S f c L)
        (points R c L S f a)) := by
  letI : Algebra R S := f.toAlgebra
  intro a
  let g : parameterRing R c L →ₐ[ℚ] S :=
    { __ := a.toRingHom
      commutes' q := RingHom.congr_fun (RingHom.ext_rat
        (a.toRingHom.comp (algebraMap ℚ (parameterRing R c L))) (algebraMap ℚ S)) q }
  let f' := g.comp (parameterCoefficient R c L)
  let b : letI : Algebra R S := f'.toAlgebra; parameterRing R c L →ₐ[R] S :=
    ContactHZeroCoefficientFunctor318.coefficientArrow R (CommRingCat.of (parameterRing R c L))
      (parameterCoefficient R c L) S g
  have hff : f=f' := by
    apply AlgHom.ext
    intro r
    exact (a.commutes r).symm
  let e := ContactArbitraryCoefficientCongrRebuild318.zeroIso R c L S f f' a b hff rfl
  have he : IsEmpty ↑(ContactGlobalSectionZero318.scheme S c
      (ContactArbitraryZeroSpecialization318.classifiedLine R c L S g)
      (ContactArbitraryZeroSpecialization318.classifiedSection R c L S g)) ↔
      IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (L' R S f c L) (points R c L S f a)) := by
    constructor
    · intro h; exact ⟨fun x => h.false (e.inv x)⟩
    · intro h; exact ⟨fun x => h.false (e.hom x)⟩
  exact (ContactArbitraryNowhereZeroOpen318.factor_iff R c L _).trans
    ((ContactArbitraryZeroSpecialization318.empty_iff R c L S g).symm.trans he)
end ContactArbitraryAffineNowhereZeroRebuild318
