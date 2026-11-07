module
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic
public section
noncomputable section
namespace IntegralDimension318
set_option maxHeartbeats 600000
variable (R S:Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S] [FaithfulSMul R S]

/-- Integral injective extensions preserve actual Krull dimension, derived
from incomparability and actual going-up chain lifting. -/
theorem dimension_eq : ringKrullDim S=ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    apply iSup_le
    intro l
    obtain ⟨P,hP⟩:=Algebra.IsIntegral.comap_surjective R S l.head
    letI:P.asIdeal.LiesOver l.head.asIdeal:=⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L,hL,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact le_sSup ⟨L,by simpa only [hL]⟩

theorem integer_polynomial_dimension : ringKrullDim (Polynomial ℤ)=2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  norm_num
end IntegralDimension318
