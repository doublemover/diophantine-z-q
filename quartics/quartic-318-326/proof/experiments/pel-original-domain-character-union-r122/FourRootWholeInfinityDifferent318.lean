module
public import FourRootAllPrimeFiniteDifferent318
public import FourRootDerivativeIdealRegular318
public import TraceDifferentPolynomialEquiv318
public section
noncomputable section
namespace FourRootWholeInfinityDifferent318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootReciprocalBranchData318 FourRootInfinityAffineComparison318
open FourRootActualInfinityRamification318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance infinityBase:Algebra ℂ[X] (I b):=(Polynomial.aeval (iz b none^2)).toAlgebra
local instance finiteBase:Algebra ℂ[X] (A b):=(Polynomial.aeval (az b none)).toAlgebra
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance finiteDedekind:IsDedekindDomain (A b):=
  FourRootActualDedekind318.finite_dedekind (branches b) (branches_injective b hb)
local instance infinityFinite:Module.Finite ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).1
local instance infinityFree:Module.Free ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
local instance finiteFinite:Module.Finite ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free (branches b)).1
local instance finiteFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free (branches b)).2
/-- The exact reciprocal polynomial-base equivalence transports the
WHOLE zero ideal, with a genuinely nonzero complex scalar factor. -/
lemma zero_ideal_image:
    (FourRootDerivativeZeroIdeals318.infinityIdeal b).map (polynomialEquivalence b hb).toRingHom=
      FourRootDerivativeZeroIdeals318.finiteIdeal (branches b):=by
  rw [FourRootDerivativeZeroIdeals318.infinityIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {equivalence b hb (FourRootDerivativeZeroIdeals318.infinityGenerator b)}=_
  rw [FourRootDerivativeIdealRegular318.infinity_image]
  have hc:IsUnit (algebraMap ℂ (A b) (FourRootDerivativeInfinityIdeal318.scaleProduct b)):=
    (IsUnit.mk0 _ (FourRootDerivativeInfinityIdeal318.scaleProduct_ne b hb)).map _
  rw [Ideal.span_singleton_mul_left_unit hc]
  rfl
/-- Genuine whole infinity TRACE-defined different equals the constructed
principal zero ideal. This is over the actual v=u² polynomial base and
retains every prime and all eight centers, not only a localized support. -/
theorem trace_equals_zero_ideal:
    differentIdeal ℂ[X] (I b)=FourRootDerivativeZeroIdeals318.infinityIdeal b:=by
  let e:=polynomialEquivalence b hb
  have hi:Function.Injective (Ideal.map e.toRingHom):=by
    intro J K h
    have hinv:e.symm.toRingHom.comp e.toRingHom=RingHom.id (I b):=by
      ext x
      exact e.symm_apply_apply x
    have h':=congrArg (Ideal.map e.symm.toRingHom) h
    simpa only [Ideal.map_map,hinv,Ideal.map_id] using h'
  apply hi
  rw [TraceDifferentPolynomialEquiv318.map_different,
    FourRootAllPrimeFiniteDifferent318.trace_equals_zero_ideal
      (branches b) (branches_injective b hb),zero_ideal_image]
end FourRootWholeInfinityDifferent318
