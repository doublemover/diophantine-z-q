module
public import ActualTwoDescentAdelicValuationSupport318
public section
noncomputable section
namespace ActualTwoDescentAdelicNormalization318
set_option maxHeartbeats 16000000

open ActualTwoDescentAdelicPairData318 ActualTwoDescentAdelicValuationSupport318
open ActualTwoDescentAdjoinThreeSupport318 ActualTwoDescentRationalSquarefree318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Supported normalization of an ACTUAL adelic class, without postulating a rational elliptic point. -/
theorem actual_adelic_normalization (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (A B : ℚ) (H : AdelicPair (∏ i, p i) A B) :
    ∃ (ε δ : ZMod 2) (u v : ι → ZMod 2), ∃ r s : ℚ, r ≠ 0 ∧ s ≠ 0 ∧
      A=(firstRepresentative p δ u : ℚ)*r^2 ∧ B=(signedSecond p ε v : ℚ)*s^2 := by
  have hsupp := actual_adelic_support p hn A B H
  letI : ∀ i, Fact (withThree p i).Prime := fun i => by
    cases i with
    | none => exact ⟨by decide⟩
    | some i => exact inferInstanceAs (Fact (p i).Prime)
  obtain ⟨w,r,hr,hA⟩ := actual_positive_supported_rational (withThree p)
    (withThree_injective p hd hp3) A H.first_pos
      (fun q hq hout => hsupp.1 q hq (hout none) (fun i => hout (some i)))
  obtain ⟨ε,v,s,hs,hB⟩ := actual_signed_supported_rational p hd B H.second_ne hsupp.2
  refine ⟨ε,w none,(fun i => w (some i)),v,r,s,hr,hs,?_,?_⟩
  · rwa [withThree_monomial] at hA
  · simpa only [signedSecond,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast] using hB

end ActualTwoDescentAdelicNormalization318
