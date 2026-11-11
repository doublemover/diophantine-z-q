module
public import ActualTwoDescentContinuousQuotientInjection318
public section
noncomputable section
namespace ActualTwoDescentGaloisImageCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentContinuousQuotientInjection318

def actualGaloisImageEquiv (n : ℚ) (hn : n ≠ 0) : DoubleQuotient n ≃ (continuousQuotientInjection n hn).range :=
  Equiv.ofBijective (fun q => ⟨continuousQuotientInjection n hn q,⟨q,rfl⟩⟩)
    ⟨fun a b h => actual_continuous_quotient_injective n hn (congrArg Subtype.val h),by
      rintro ⟨f,q,hq⟩
      exact ⟨q,Subtype.ext hq⟩⟩

lemma actual_galois_image_card (n : ℚ) (hn : n ≠ 0) :
    Nat.card (continuousQuotientInjection n hn).range=Nat.card (DoubleQuotient n) :=
  (Nat.card_congr (actualGaloisImageEquiv n hn)).symm

/-- The actual continuous cocycle image retains the unresolved four/eight alternative. -/
theorem actual_galois_image_alternative (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n))
    (hb : Nat.card (DoubleQuotient n) ≤ 8) :
    Nat.card (continuousQuotientInjection n hn).range=4 ∨ Nat.card (continuousQuotientInjection n hn).range=8 := by
  rw [actual_galois_image_card]
  exact ActualTwoDescentRationalQuotientAlternative318.actual_quotient_four_or_eight n hn hf hb

end ActualTwoDescentGaloisImageCardinality318
