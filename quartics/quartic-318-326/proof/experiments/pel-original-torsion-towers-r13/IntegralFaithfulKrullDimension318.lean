module
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public section
noncomputable section
namespace IntegralFaithfulKrullDimension318
open Order
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S] [FaithfulSMul R S]
/-- Actual integral incomparability and full going-up chain lifting
preserve native Krull dimension for a faithful integral algebra. -/
lemma dimension : ringKrullDim S=ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under (R := R) (I := P.asIdeal) hPQ
  · change (⨆ l : LTSeries (PrimeSpectrum R), (l.length : WithBot ℕ∞))≤_
    apply iSup_le
    intro l
    obtain ⟨P,hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
    letI : P.asIdeal.LiesOver l.head.asIdeal :=
      ⟨congrArg PrimeSpectrum.asIdeal hP.symm⟩
    obtain ⟨L,hL,_,_⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    rw [←hL]
    exact L.length_le_krullDim
end IntegralFaithfulKrullDimension318
