module
public import OriginalPrimeOrderInertia318
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public section
noncomputable section
namespace OriginalNormalClosureGalois318
open Polynomial
universe u
variable (L : Type u) [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

@[expose] def baseAlgebra : Algebra ℚ[X] L :=
  ((algebraMap (RatFunc ℚ) L).comp (algebraMap ℚ[X] (RatFunc ℚ))).toAlgebra
-- Preserve the native polynomial action on RatFunc; this is only the fallback
-- composite action on a genuine field extension.
attribute [instance 100] baseAlgebra
instance baseTower : IsScalarTower ℚ[X] (RatFunc ℚ) L :=
  IsScalarTower.of_algebraMap_eq (R := ℚ[X]) (S := RatFunc ℚ) (A := L) (fun _ => rfl)

/-- The literal integral closure inside the ORIGINAL field. -/
abbrev Order := integralClosure ℚ[X] L
abbrev Group := L ≃ₐ[RatFunc ℚ] L

instance originalFraction : IsFractionRing (Order L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) L (Order L)
instance originalDedekind : IsDedekindDomain (Order L) :=
  IsIntegralClosure.isDedekindDomain ℚ[X] (RatFunc ℚ) L (Order L)
instance originalFinite : Module.Finite ℚ[X] (Order L) :=
  IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) L (Order L)
instance originalFree : Module.Free ℚ[X] (Order L) := by
  letI : Module.IsTorsionFree ℚ[X] L := .trans_faithfulSMul ℚ[X] (RatFunc ℚ) L
  exact IsIntegralClosure.module_free ℚ[X] (RatFunc ℚ) L (Order L)
instance originalFlat : Module.Flat ℚ[X] (Order L) := Module.Flat.of_free

/-- The actual original generic Galois group acts on its literal integral closure. -/
instance originalAction : MulSemiringAction (Group L) (Order L) :=
  IsIntegralClosure.MulSemiringAction ℚ[X] (RatFunc ℚ) L (Order L)
instance originalGaloisGroup : IsGaloisGroup (Group L) ℚ[X] (Order L) :=
  IsGaloisGroup.of_isFractionRing (Group L) ℚ[X] (Order L) (RatFunc ℚ) L

@[expose] def affineAction (σ : Group L) : Order L ≃+* Order L :=
  (galRestrict ℚ[X] (RatFunc ℚ) L (Order L) σ).toRingEquiv

lemma affineAction_smul (σ : Group L) (b : Order L) :
    affineAction L σ b = σ • b := rfl
lemma affineAction_generic (σ : Group L) (b : Order L) :
    σ (algebraMap (Order L) L b) = algebraMap (Order L) L (affineAction L σ b) :=
  (algebraMap_galRestrict_apply ℚ[X] σ b).symm

lemma coefficient_square (q : ℚ[X]) :
    algebraMap (Order L) L (algebraMap ℚ[X] (Order L) q) =
      algebraMap (RatFunc ℚ) L (algebraMap ℚ[X] (RatFunc ℚ) q) := by
  rw [← IsScalarTower.algebraMap_apply ℚ[X] (Order L) L]
  all_goals rfl

instance baseFaithful : FaithfulSMul ℚ[X] (Order L) := by
  apply (faithfulSMul_iff_algebraMap_injective ℚ[X] (Order L)).mpr
  intro a b h
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  apply (algebraMap (RatFunc ℚ) L).injective
  simpa only [coefficient_square] using congrArg (algebraMap (Order L) L) h

/-- All closed base residue extensions are separable, including nonrational
polynomial primes, because the actual base residue field has characteristic zero. -/
theorem residue_separable (p : Ideal ℚ[X]) [p.IsPrime] :
    Algebra.HasSeparableResidueFieldsAt ℚ[X] (Order L) p := by
  letI : Algebra ℚ p.ResidueField :=
    ((algebraMap ℚ[X] p.ResidueField).comp (algebraMap ℚ ℚ[X])).toAlgebra
  letI : CharZero p.ResidueField := Algebra.charZero_of_charZero ℚ p.ResidueField
  infer_instance
end OriginalNormalClosureGalois318
