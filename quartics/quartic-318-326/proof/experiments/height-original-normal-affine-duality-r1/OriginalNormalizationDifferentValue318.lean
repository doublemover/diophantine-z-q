module
public import IntegralFourRootNormalizationConductor318
public import OriginalNormalCenterDualImage318
public section
noncomputable section
namespace OriginalNormalizationDifferentValue318
open Polynomial NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "B" => SourceOpenRing c t w D
local notation "a" => contacts c t w

lemma field_scalar (r : R) : M.fieldPoint (algebraMap R B r)=algebraMap R (K c t) r := by
  have h := M.field_polynomial (Polynomial.C r)
  rw [Polynomial.aeval_C] at h
  simpa only [IsScalarTower.algebraMap_apply R R[X]
    (IntegralDistinctContactOpen318.Base R a D.coefficients),
    IsScalarTower.algebraMap_apply R
      (IntegralDistinctContactOpen318.Base R a D.coefficients) B] using h

/-- The SAME original point evaluation, now explicitly as a V-algebra
map. No independent evaluation or sign choice is introduced. -/
@[expose] def evaluation : B →ₐ[R] K c t where
  toRingHom := M.fieldPoint
  commutes' := field_scalar c t w D M

@[expose] def differentValue : K c t :=
  evaluation c t w D M (IntegralFourRootNormalizationConductor318.different R a D.coefficients)
lemma differentValue_ne : differentValue c t w D M ≠ 0 :=
  ((IntegralFourRootNormalizationConductor318.different_isUnit R a D.coefficients).map
    (evaluation c t w D M).toRingHom).ne_zero

/-- Literal evaluation of the original marked raw different, including
its factor16 and every normalized signed root. -/
lemma differentValue_eq : differentValue c t w D M =
    16 * ∏ i : Fin 4,D.normalizedRoots i := by
  unfold differentValue IntegralFourRootNormalizationConductor318.different
  simp only [Algebra.smul_def,map_mul,map_ofNat,FourRootTraceCoefficient318.rootProduct_eq,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact M.field_roots i

/-- The normalization multiplier is retained exactly when passing back
to the ORIGINAL signed roots. Equality of squareclasses is insufficient. -/
lemma original_signed_different :
    16 * (∏ i : Fin 4,RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)) =
    (∏ i : Fin 4,D.multiplier i) * differentValue c t w D M := by
  rw [differentValue_eq]
  have he (i : Fin 4) : RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i)=
      D.multiplier i*D.normalizedRoots i := (D.original_signed_root i).symm
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  ring

lemma inverse_different_value :
    evaluation c t w D M
      (↑((IntegralFourRootNormalizationConductor318.different_isUnit R a D.coefficients).unit⁻¹) : B)=
        (differentValue c t w D M)⁻¹ := by
  apply mul_left_cancel₀ (differentValue_ne c t w D M)
  rw [mul_inv_cancel₀ (differentValue_ne c t w D M)]
  change evaluation c t w D M _ * evaluation c t w D M _=1
  rw [←map_mul,←(IntegralFourRootNormalizationConductor318.different_isUnit R a D.coefficients).unit_spec,
    Units.mul_inv,map_one]
end OriginalNormalizationDifferentValue318
