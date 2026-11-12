module
public import ActualTwoDescentOriginalQuotientProducer318
public section
noncomputable section
namespace ActualTwoDescentFourQuotientPointConsumer318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentActualQuotientControl318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentPointExtraction318 TwoTwistPointRealization318

/-- Once the actual quotient cardinalities are eight, BOTH rational points
at all FOUR already-fixed pole labels are extracted without changing labels,
parameters or source indices. These cardinality equalities remain explicit. -/
theorem actual_four_realizations_of_quotient_eight
    (b c d : Fin 4 → ℚ) (beta theta n : Fin 4 → ℕ)
    (hb : ∀ i, beta i ≠ 0) (hc : ∀ i, c i ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hB : ∀ i, 17*b i=(beta i : ℚ)*(c i)^2)
    (hV : ∀ i, (17*b i)^2*(1-b i/17)=(theta i : ℚ)*(d i)^2)
    (C : ∀ i, QuotientControl (n i) (beta i))
    (Ctwist : ∀ i, QuotientControl (n i*theta i) (beta i))
    (hcard : ∀ i, Nat.card (DoubleQuotient (n i : ℚ))=8)
    (hcardtwist : ∀ i, Nat.card (DoubleQuotient ((n i*theta i : ℕ) : ℚ))=8) :
    Nonempty (∀ i, Realization (b i)) := by
  let P : ∀ i, KummerPoint (beta i : ℚ) (n i : ℚ) :=
    fun i => Classical.choice ((C i).2.2.2 (hcard i))
  let Q : ∀ i, KummerPoint (beta i : ℚ) ((n i : ℚ)*(theta i : ℚ)) := by
    intro i
    simpa only [Nat.cast_mul] using Classical.choice ((Ctwist i).2.2.2 (hcardtwist i))
  exact ⟨actual_four_realizations b (fun i => (beta i : ℚ)) (fun i => (theta i : ℚ))
    c d (fun i => (n i : ℚ)) (fun i => by exact_mod_cast hb i) hc hd hB hV P Q⟩

end ActualTwoDescentFourQuotientPointConsumer318
