module
public import OriginalNormalizationConductorNonzero318
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace OriginalNormalizationIntegralEvaluation318
open Polynomial NumberField ActualFinitePlaceIntegers318
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationDifferentValue318 OriginalNormalizationConductorSpecialization318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "B" => SourceOpenRing c t w D
local notation "a" => contacts c t w
variable (ht : w (t : K c t) ≤ 1)

/-- The actual integral finite-coordinate branch of the original point.
No statement here says that every place belongs to this branch. -/
@[expose] def integralCoordinate : R := ⟨(t : K c t),(bounded_iff w _).mp ht⟩

lemma polynomial_value (p : Polynomial R) : M.fieldPoint (algebraMap (Polynomial R) B p)=
    Polynomial.aeval (t : K c t) p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial R)
    (IntegralDistinctContactOpen318.Base R a D.coefficients) B]
  exact M.field_polynomial p

lemma polynomial_square :
    (algebraMap R (K c t)).comp (Polynomial.evalRingHom (integralCoordinate c t w ht))=
      M.fieldPoint.comp (algebraMap (Polynomial R) B) := by
  have he : (algebraMap R (K c t)).comp (Polynomial.evalRingHom (integralCoordinate c t w ht))=
      (Polynomial.aeval (t : K c t)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      change algebraMap R (K c t) r=algebraMap R (K c t) r
      rfl
    · change algebraMap R (K c t) (integralCoordinate c t w ht)=(t : K c t)
      rfl
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply,polynomial_value]
  exact RingHom.congr_fun he p

include ht in
/-- The actual NORMAL-order value is integral at this exact original
finite-coordinate point, by mapping its monic equation along the actual
polynomial evaluation square. No normal-order point map is assumed. -/
lemma normal_value_integral (z : IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients) :
    IsIntegral R (evaluation c t w D M z.val) :=
  IsIntegral.map_of_comp_eq (Polynomial.evalRingHom (integralCoordinate c t w ht))
    M.fieldPoint (polynomial_square c t w D M ht) z.property

include ht in
lemma normal_value_bound (z : IntegralFourRootNormalizationConductor318.normalOrder R a D.coefficients) :
    w (evaluation c t w D M z.val) ≤ 1 := by
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (normal_value_integral c t w D M ht z)
  rw [←hr]
  exact integer_bound w r

include ht in
/-- Every actual conductor value is integral on the selected finite
branch. This is the whole image, not just the denominator witness. -/
lemma conductorValues_bounded (y : K c t) (hy : y ∈ conductorValues c t w D M) : w y ≤ 1 := by
  obtain ⟨z,hz,rfl⟩ := hy
  exact normal_value_bound c t w D M ht
    ⟨z,IntegralFourRootNormalizationConductor318.conductor_le_normal R a D.coefficients hz⟩
end OriginalNormalizationIntegralEvaluation318
