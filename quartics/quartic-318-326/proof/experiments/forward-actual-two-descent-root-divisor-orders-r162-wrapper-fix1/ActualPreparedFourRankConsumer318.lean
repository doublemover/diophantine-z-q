module
public import ActualPreparedPoleSquarefreeClasses318
public import ActualTwoDescentFourInfinitePointConsumer318
public section
noncomputable section
namespace ActualPreparedFourRankConsumer318
open ActualPreparedPoleSquarefreeClasses318
open ActualTwoDescentEllipticModel318 ActualTwoDescentMordellWeilControl318
open ActualTwoDescentFourInfinitePointConsumer318 TwoTwistPointRealization318

/-- Exact same-pole extraction from the genuine rational-group inputs.
No rank, Sha-finiteness, reduced-duality or local-to-global producer is hidden:
both infinitude hypotheses and both Mordell-Weil controls remain explicit. -/
theorem from_classes (b : Fin 4 → ℚ) (C : ∀ i, Classes (b i))
    (n : Fin 4 → ℕ)
    (hMW : ∀ i, MordellWeilControl (n i) (C i).beta)
    (hMWtwist : ∀ i, MordellWeilControl (n i*(C i).theta) (C i).beta)
    (hInfinite : ∀ i, Infinite (Point (n i : ℚ)))
    (hInfiniteTwist : ∀ i, Infinite (Point ((n i*(C i).theta : ℕ) : ℚ))) :
    Nonempty (∀ i, Realization (b i)) := by
  exact actual_four_realizations_of_infinite b (fun i => (C i).c) (fun i => (C i).d)
    (fun i => (C i).beta) (fun i => (C i).theta) n
    (fun i => ne_of_gt (C i).beta_pos) (fun i => (C i).c_ne) (fun i => (C i).d_ne)
    (fun i => (C i).first_class) (fun i => (C i).second_class)
    hMW hMWtwist hInfinite hInfiniteTwist

/-- The actual four poles determine positive squarefree classes BEFORE the
simultaneous twist parameters are chosen. The remaining arithmetic support
and genuine global rank conditions are not inferred from positivity. -/
theorem range_to_conditional_realizations (b : Fin 4 → ℚ)
    (hpos : ∀ i, 0<b i) (hsmall : ∀ i, b i<17) :
    ∃ C : ∀ i, Classes (b i), ∀ n : Fin 4 → ℕ,
      (∀ i, MordellWeilControl (n i) (C i).beta) →
      (∀ i, MordellWeilControl (n i*(C i).theta) (C i).beta) →
      (∀ i, Infinite (Point (n i : ℚ))) →
      (∀ i, Infinite (Point ((n i*(C i).theta : ℕ) : ℚ))) →
      Nonempty (∀ i, Realization (b i)) := by
  let C : ∀ i, Classes (b i) :=
    fun i => Classical.choice (classes_exist (b i) (hpos i) (hsmall i))
  exact ⟨C, fun n hMW hMWtwist hInfinite hInfiniteTwist =>
    from_classes b C n hMW hMWtwist hInfinite hInfiniteTwist⟩

end ActualPreparedFourRankConsumer318
