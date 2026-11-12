module
public import ActualTwoDescentOriginalMordellWeilProducer318
public section
noncomputable section
namespace ActualTwoDescentFourInfinitePointConsumer318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentMordellWeilControl318
open ActualTwoDescentPointExtraction318 TwoTwistPointRealization318

/-- The exact remaining global input can now be stated simply as infinitude
of the ACTUAL rational groups at both twists for each fixed source pole.
Finite generation, upper rank, torsion, Kummer and extraction are already proved. -/
theorem actual_four_realizations_of_infinite
    (b c d : Fin 4 → ℚ) (beta theta n : Fin 4 → ℕ)
    (hb : ∀ i, beta i ≠ 0) (hc : ∀ i, c i ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hB : ∀ i, 17*b i=(beta i : ℚ)*(c i)^2)
    (hV : ∀ i, (17*b i)^2*(1-b i/17)=(theta i : ℚ)*(d i)^2)
    (C : ∀ i, MordellWeilControl (n i) (beta i))
    (Ctwist : ∀ i, MordellWeilControl (n i*theta i) (beta i))
    (hInfinite : ∀ i, Infinite (Point (n i : ℚ)))
    (hInfiniteTwist : ∀ i, Infinite (Point ((n i*theta i : ℕ) : ℚ))) :
    Nonempty (∀ i, Realization (b i)) := by
  let P : ∀ i, KummerPoint (beta i : ℚ) (n i : ℚ) :=
    fun i => Classical.choice ((C i).2.2.2.2 (hInfinite i))
  let Q : ∀ i, KummerPoint (beta i : ℚ) ((n i : ℚ)*(theta i : ℚ)) := by
    intro i
    simpa only [Nat.cast_mul] using Classical.choice ((Ctwist i).2.2.2.2 (hInfiniteTwist i))
  exact ⟨actual_four_realizations b (fun i => (beta i : ℚ)) (fun i => (theta i : ℚ))
    c d (fun i => (n i : ℚ)) (fun i => by exact_mod_cast hb i) hc hd hB hV P Q⟩

end ActualTwoDescentFourInfinitePointConsumer318
