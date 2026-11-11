module
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public section
noncomputable section
namespace WholeFiniteFractionExtension318
open scoped nonZeroDivisors
variable (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- WHOLE finite faithful normalization produces a finite extension of
the genuine fraction fields, with the actual lifted inclusion. -/
theorem finite : Module.Finite (FractionRing R) (FractionRing A) := by
  letI : Algebra.IsAlgebraic R A := ⟨fun a => (IsIntegral.of_finite R a).isAlgebraic⟩
  letI : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) A⁰
  letI : Algebra.IsAlgebraic R (FractionRing A) :=
    Algebra.IsAlgebraic.trans R A (FractionRing A)
  letI : Algebra.IsAlgebraic (FractionRing R) (FractionRing A) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  letI : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) A⁰
  letI : Algebra.EssFiniteType R (FractionRing A) :=
    Algebra.EssFiniteType.comp R A (FractionRing A)
  letI : Algebra.EssFiniteType (FractionRing R) (FractionRing A) :=
    Algebra.EssFiniteType.of_comp R (FractionRing R) (FractionRing A)
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- The field scalar action extends EXACTLY the given whole-ring
normalization inclusion; no separately chosen field isomorphism occurs. -/
lemma coefficient_square :
    (algebraMap (FractionRing R) (FractionRing A)).comp
      (algebraMap R (FractionRing R)) =
    (algebraMap A (FractionRing A)).comp (algebraMap R A) := by
  rw [←IsScalarTower.algebraMap_eq R (FractionRing R) (FractionRing A),
    ←IsScalarTower.algebraMap_eq R A (FractionRing A)]
end WholeFiniteFractionExtension318
