module
public import ActualTwoDescentSimultaneousQuadrics318
public import ActualPreparedDescentInterface318
public section
noncomputable section
namespace ActualPreparedFourCoverConsumer318
open ActualTwoDescentRationalCover318 ActualTwoDescentPointExtraction318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleMutualRoots318
open ActualTwoDescentMordellWeilControl318 TwoTwistPointRealization318

/-- At the exact prepared poles, finite simultaneous descent constructs
the original two twists for every index. Concrete rational quadratic-cover
coordinates, rather than rank/infinitude, are the remaining inputs. The cover
inputs are explicit global rational data; their existence is NOT concluded
from preparation or from the Mordell-Weil controls. -/
theorem actual_four_prepared_covers (b : Fin 4 → ℚ)
    (H : ∀ i, Preparation (b i)) (N : ℕ) :
    ∃ (C : ∀ i, Classes (b i)) (n : Fin 4 → ℕ),
      (∀ i, N<n i ∧ Squarefree (n i) ∧ Squarefree (n i*(C i).theta) ∧
        (n i:ZMod 12)=11 ∧ (n i*(C i).theta:ZMod 12)=11 ∧
        MordellWeilControl (n i) (C i).beta ∧
        MordellWeilControl (n i*(C i).theta) (C i).beta) ∧
      ((∀ i, Cover ((C i).beta:ℚ) (n i:ℚ)) →
        (∀ i, Cover ((C i).beta:ℚ) ((n i:ℚ)*((C i).theta:ℚ))) →
        Nonempty (∀ i, Realization (b i))) := by
  obtain ⟨C,n,hn,_⟩ :=
    ActualPreparedDescentInterface318.actual_four_prepared_poles b H N
  refine ⟨C,n,hn,?_⟩
  intro P Q
  exact ⟨fun i => actual_realization_of_kummer (b i) (C i).beta (C i).theta
    (C i).c (C i).d (n i:ℚ)
    (by exact_mod_cast (Nat.ne_of_gt (C i).beta_pos)) (C i).c_ne (C i).d_ne
    (C i).first_class (C i).second_class (P i).toKummer (Q i).toKummer⟩

end ActualPreparedFourCoverConsumer318
