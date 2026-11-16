module
public import ActualTwoDescentInfinityNativeDomain318
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Localization.Submodule
public section
noncomputable section
namespace ActualTwoDescentInfinityNativeDVR318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityMaximalGenerator318 ActualTwoDescentInfinityNativeDomain318
variable {K : Type*} [Field K] [CharZero K]

instance infinityChartNoetherian (n : K) : IsNoetherianRing (InfinityChart n) :=
  isNoetherianRing_of_surjective (Polynomial (Polynomial K)) (InfinityChart n)
    (AdjoinRoot.mk (infinityPolynomial n)) AdjoinRoot.mk_surjective
instance infinityLocalNoetherian (n : K) : IsNoetherianRing (InfinityLocalRing n) :=
  IsLocalization.isNoetherianRing (originIdeal n).primeCompl (InfinityLocalRing n) inferInstance

lemma actual_infinity_maximal_nonzero (n : K) :
    IsLocalRing.maximalIdeal (InfinityLocalRing n) ≠ ⊥ := by
  intro h
  have hu := actual_local_u_in_maximal n
  rw [h,Ideal.mem_bot] at hu
  exact actual_local_u_nonzero n hu

/-- The ORIGINAL local ring at O is a native DVR. Every premise is
produced: Noetherianity, integrality, nonfieldness and m=(u). -/
instance infinityNativeDVR (n : K) : IsDiscreteValuationRing (InfinityLocalRing n) := by
  have hn : ¬IsField (InfinityLocalRing n) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (actual_infinity_maximal_nonzero n)
  have hp : (IsLocalRing.maximalIdeal (InfinityLocalRing n)).IsPrincipal := by
    rw [actual_infinity_maximal_principal]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (InfinityLocalRing n) hn).out 5 1).mp hp

/-- Actual u, not an arbitrary newly chosen uniformizer, generates m. -/
lemma actual_infinity_u_irreducible (n : K) : Irreducible (localU n) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (localU n)
    (actual_local_u_nonzero n) (actual_infinity_maximal_principal n)

end ActualTwoDescentInfinityNativeDVR318
