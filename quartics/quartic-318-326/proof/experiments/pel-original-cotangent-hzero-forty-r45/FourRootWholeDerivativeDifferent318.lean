module
public import FourRootWholeInfinityDifferent318
public import FourRootEffectiveDerivativeZero318
public import ActualQuotientKernelCharts318
public section
noncomputable section
namespace FourRootWholeDerivativeDifferent318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318 FourRootDerivativeZeroIdeals318
open FourRootDerivativeIdealClosed318 ActualQuotientKernelCharts318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev A:=FourRootAffineCoordinateRing318.Ring b
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance finiteBase:Algebra ℂ[X] (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance infinityBase:Algebra ℂ[X] (I b):=
  (Polynomial.aeval (FourRootInfinityCoordinateRing318.coordinate b none^2)).toAlgebra
local instance finiteDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance finiteFree:Module.Free ℂ[X] (A b):=(FourRootActualOrderGalois318.finite_free b).2
local instance infinityFree:Module.Free ℂ[X] (I b):=(FourRootSquaredInfinityBase318.finite_free b).2
@[expose] def finiteOpen:(FourRootGluedScheme318.scheme b).affineOpens:=
  chartOpen (CommRingCat.of (A b)) (FourRootGluedScheme318.finiteChart b)
@[expose] def infinityOpen:(FourRootGluedScheme318.scheme b).affineOpens:=
  chartOpen (CommRingCat.of (I b)) (FourRootGluedScheme318.infinityChart b)
/-- Exact original coefficients, through Gamma-Spec and the ACTUAL
whole-chart open immersion, identify the actual global kernel ideal
with the independently TRACE-defined whole finite different. -/
theorem finite_trace_kernel:
    ((idealSheaf b).ideal (finiteOpen b)).comap
      (coefficient (CommRingCat.of (A b)) (FourRootGluedScheme318.finiteChart b)).hom=
        differentIdeal ℂ[X] (A b):=by
  change ((into b).ker.ideal (finiteOpen b)).comap _=_
  rw [original_kernel (CommRingCat.of (A b)) (finiteIdeal b) (into b)
    (FourRootGluedScheme318.finiteChart b) (finiteChart b) (finite_square b)]
  exact (FourRootAllPrimeFiniteDifferent318.trace_equals_zero_ideal b hb).symm
/-- The SAME actual ideal-sheaf data on the entire infinity chart is
its original v=u² trace different. It retains every scheme prime and
every one of the eight infinity centers, without any radical or support
replacement. -/
theorem infinity_trace_kernel:
    ((idealSheaf b).ideal (infinityOpen b)).comap
      (coefficient (CommRingCat.of (I b)) (FourRootGluedScheme318.infinityChart b)).hom=
        differentIdeal ℂ[X] (I b):=by
  change ((into b).ker.ideal (infinityOpen b)).comap _=_
  rw [original_kernel (CommRingCat.of (I b)) (infinityIdeal b) (into b)
    (FourRootGluedScheme318.infinityChart b) (infinityChart b) (infinity_square b)]
  exact (FourRootWholeInfinityDifferent318.trace_equals_zero_ideal b hb).symm
/-- Both covering affine descriptions are the exact independent trace
ideals. The constructed closed subscheme also has the produced regular
principal quotient neighborhoods from EffectiveDerivativeZero318.
The ideal, derivative source line and intrinsic canonical line are not
identified with one another. -/
theorem whole_trace_identification:
    (((idealSheaf b).ideal (finiteOpen b)).comap
      (coefficient (CommRingCat.of (A b)) (FourRootGluedScheme318.finiteChart b)).hom=
        differentIdeal ℂ[X] (A b)) ∧
    (((idealSheaf b).ideal (infinityOpen b)).comap
      (coefficient (CommRingCat.of (I b)) (FourRootGluedScheme318.infinityChart b)).hom=
        differentIdeal ℂ[X] (I b)):=
  ⟨finite_trace_kernel b hb,infinity_trace_kernel b hb⟩
end FourRootWholeDerivativeDifferent318
