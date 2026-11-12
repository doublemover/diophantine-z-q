module
public import IntegralDistinctContactOpen318
public import NormalizedGenericChartMaps318
public section
noncomputable section
namespace IntegralNormalSourcePoint318
open Polynomial IntegralDistinctContactOpen318 IntegralRootPointMaps318
set_option maxHeartbeats 1000000
variable (R K : Type*) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (a d : Fin 4 → R) (t : K)
  (hd : ∀ i, algebraMap R K (d i) ≠ 0)
  (ht : t ≠ 0) (hn : ∀ i, t-algebraMap R K (a i) ≠ 0)

include hd ht hn in
theorem denominator_unit : IsUnit ((Polynomial.aeval t)
    (IntegralReciprocalBase318.finiteDenominator R a (arithmeticDenominator R d))) := by
  apply IsUnit.mk0
  simp only [IntegralReciprocalBase318.finiteDenominator, arithmeticDenominator,
    map_mul, map_prod, map_ofNat, Polynomial.aeval_C, Polynomial.aeval_X, map_sub]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)))
    (mul_ne_zero ht (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)))

@[expose] def baseEvaluation : Base R a d →+* K :=
  IsLocalization.Away.lift (g := (Polynomial.aeval t).toRingHom)
    (IntegralReciprocalBase318.finiteDenominator R a (arithmeticDenominator R d))
    (denominator_unit R K a d t hd ht hn)
theorem baseEvaluation_polynomial (p : R[X]) :
    baseEvaluation R K a d t hd ht hn (algebraMap R[X] (Base R a d) p) =
      Polynomial.aeval t p := IsLocalization.Away.lift_eq _ _ p

variable (z : Fin 4 → K)
  (hz : ∀ i, (z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i)))
@[expose] def openMap : OpenOrder R a d →+* K := by
  letI : Algebra (Base R a d) K := (baseEvaluation R K a d t hd ht hn).toAlgebra
  apply (fourMap (fun i => algebraMap R[X] (Base R a d)
    (DistinctContactIntegralDomain318.coefficient R a d i)) z ?_).toRingHom
  intro i
  change (z i)^2 = baseEvaluation R K a d t hd ht hn
    (algebraMap R[X] (Base R a d) (DistinctContactIntegralDomain318.coefficient R a d i))
  rw [baseEvaluation_polynomial]
  simpa only [DistinctContactIntegralDomain318.coefficient, map_mul, map_sub,
    Polynomial.aeval_C, Polynomial.aeval_X] using hz i

theorem openMap_base (r : Base R a d) :
    openMap R K a d t hd ht hn z hz (algebraMap (Base R a d) (OpenOrder R a d) r) =
      baseEvaluation R K a d t hd ht hn r := by
  letI : Algebra (Base R a d) K := (baseEvaluation R K a d t hd ht hn).toAlgebra
  exact (fourMap _ _ _).commutes r

theorem openMap_root (i : Fin 4) :
    openMap R K a d t hd ht hn z hz
      (FourRootOrderSigns318.generator (fun j => algebraMap R[X] (Base R a d)
        (DistinctContactIntegralDomain318.coefficient R a d j)) i) = z i := by
  letI : Algebra (Base R a d) K := (baseEvaluation R K a d t hd ht hn).toAlgebra
  exact fourMap_generator _ _ _ i

/-- This is the literal original polynomial-order map into the localized
four-root order, retaining all four marked generators. -/
@[expose] def sourceInclusion : Source R a d →+* OpenOrder R a d :=
  (FourRootSignBaseChange318.coefficientMap
    (DistinctContactIntegralDomain318.coefficient R a d) (Base R a d)).toRingHom

theorem sourceInclusion_polynomial (p : R[X]) :
    sourceInclusion R a d (algebraMap R[X] (Source R a d) p) =
      algebraMap (Base R a d) (OpenOrder R a d) (algebraMap R[X] (Base R a d) p) := by
  rw [←IsScalarTower.algebraMap_apply]
  exact (FourRootSignBaseChange318.coefficientMap _ _).commutes p

theorem sourceInclusion_root (i : Fin 4) :
    sourceInclusion R a d (FourRootOrderSigns318.generator
      (DistinctContactIntegralDomain318.coefficient R a d) i) =
      FourRootOrderSigns318.generator (fun j => algebraMap R[X] (Base R a d)
        (DistinctContactIntegralDomain318.coefficient R a d j)) i :=
  FourRootSignBaseChange318.coefficientMap_generator _ _ i

/-- Equality of the WHOLE original signed point, rather than merely equality
of its coordinate or its four squared roots. -/
theorem full_source_point :
    (openMap R K a d t hd ht hn z hz).comp (sourceInclusion R a d) =
      NormalizedGenericChartMaps318.finiteMap R K d a t z hz := by
  apply four_ringHom_ext
  · apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, sourceInclusion_polynomial, openMap_base,
      baseEvaluation_polynomial, NormalizedGenericChartMaps318.finite_polynomial]
  · intro i
    simp only [RingHom.comp_apply, sourceInclusion_root, openMap_root,
      NormalizedGenericChartMaps318.finite_generator]
end IntegralNormalSourcePoint318
