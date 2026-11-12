module
public import ActualTwoDescentContinuousGaloisCocycles318
public section
noncomputable section
namespace ActualTwoDescentContinuousQuotientInjection318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentContinuousGaloisCocycles318

def continuousQuotientInjection (n : ℚ) (hn : n ≠ 0) : DoubleQuotient n →* continuousCocycles n :=
  (QuotientGroup.kerLift (continuousConnectingHom n hn)).comp
    (QuotientGroup.quotientMulEquivOfEq (actual_continuous_connecting_kernel n hn).symm).toMonoidHom

lemma actual_continuous_quotient_injective (n : ℚ) (hn : n ≠ 0) :
    Function.Injective (continuousQuotientInjection n hn) :=
  (QuotientGroup.kerLift_injective (continuousConnectingHom n hn)).comp
    (QuotientGroup.quotientMulEquivOfEq (actual_continuous_connecting_kernel n hn).symm).injective

lemma actual_continuous_quotient_mk (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    continuousQuotientInjection n hn (QuotientGroup.mk (Multiplicative.ofAdd P))=
      continuousConnectingHom n hn (Multiplicative.ofAdd P) := rfl

end ActualTwoDescentContinuousQuotientInjection318
