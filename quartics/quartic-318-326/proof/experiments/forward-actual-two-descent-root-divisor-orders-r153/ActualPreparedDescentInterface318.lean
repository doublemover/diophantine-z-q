module
public import ActualPreparedPoleResidues318
public import ActualPreparedFiniteGlobalInterface318
public section
noncomputable section
namespace ActualPreparedDescentInterface318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleMutualRoots318
open ActualTwoDescentMordellWeilControl318 ActualTwoDescentEllipticModel318
open TwoTwistPointRealization318

/-- Coprimality of the literal coefficient representatives is a consequence
of the SAME pole's preparation, not a separately supplied support assumption. -/
theorem coefficient_coprime {b : ℚ} (C : Classes b) (H : Preparation b) :
    Nat.Coprime C.beta C.theta := by
  apply Nat.coprime_of_dvd
  intro p hp hpb hpt
  letI : Fact p.Prime := ⟨hp⟩
  exact disjoint_support C H hpb hpt

/-- Assemble actual preparation with finite simultaneous descent, while
deriving the two coefficient residue laws from that preparation. Neither
mutual symbols nor prime arrays nor Mordell-Weil controls are caller inputs.
Both genuine rational-group infinitude conditions remain in the final implication. -/
theorem from_preparation {b : ℚ} (C : Classes b) (H : Preparation b)
    (N : ℕ) :
    ∃ n : ℕ, N<n ∧ Squarefree n ∧ Squarefree (n*C.theta) ∧
      (n:ZMod 12)=11 ∧ (n*C.theta:ZMod 12)=11 ∧
      MordellWeilControl n C.beta ∧ MordellWeilControl (n*C.theta) C.beta ∧
      (Infinite (Point (n:ℚ)) → Infinite (Point ((n*C.theta:ℕ):ℚ)) →
        Nonempty (Realization b)) := by
  obtain ⟨hBeta24,hTheta24⟩ := ActualPreparedPoleResidues318.coefficients_mod24 C H
  obtain ⟨hTheta,hBeta⟩ := mutual_roots C H
  apply ActualPreparedFiniteGlobalInterface318.from_classes C hBeta24 hTheta24
    (coefficient_coprime C H) _ _ N
  · intro p hp hpb
    obtain ⟨r,_,hr⟩ := hTheta p hpb
    exact ⟨r,hr⟩
  · intro p hp hpt
    obtain ⟨r,_,hr⟩ := hBeta p hpt
    exact ⟨r,hr⟩

/-- Positive squarefree classes are chosen from the literal actual pole,
then finite descent is constructed. The caller supplies no residue, support,
mutual-symbol, prime-array, or Mordell-Weil-control data. -/
theorem actual_prepared_pole {b : ℚ} (H : Preparation b) (N : ℕ) :
    ∃ C : Classes b, ∃ n : ℕ, N<n ∧ Squarefree n ∧ Squarefree (n*C.theta) ∧
      (n:ZMod 12)=11 ∧ (n*C.theta:ZMod 12)=11 ∧
      MordellWeilControl n C.beta ∧ MordellWeilControl (n*C.theta) C.beta ∧
      (Infinite (Point (n:ℚ)) → Infinite (Point ((n*C.theta:ℕ):ℚ)) →
        Nonempty (Realization b)) := by
  let C : Classes b := Classical.choice (classes_exist b H.positive H.small)
  exact ⟨C,from_preparation C H N⟩

/-- All four actual poles are retained at the same source index. The only
remaining global implication inputs are infinitude of the actual rational
point groups on BOTH constructed twists for each pole. -/
theorem actual_four_prepared_poles (b : Fin 4 → ℚ)
    (H : ∀ i, Preparation (b i)) (N : ℕ) :
    ∃ (C : ∀ i, Classes (b i)) (n : Fin 4 → ℕ),
      (∀ i, N<n i ∧ Squarefree (n i) ∧ Squarefree (n i*(C i).theta) ∧
        (n i:ZMod 12)=11 ∧ (n i*(C i).theta:ZMod 12)=11 ∧
        MordellWeilControl (n i) (C i).beta ∧
        MordellWeilControl (n i*(C i).theta) (C i).beta) ∧
      ((∀ i, Infinite (Point (n i:ℚ))) →
        (∀ i, Infinite (Point ((n i*(C i).theta:ℕ):ℚ))) →
        Nonempty (∀ i, Realization (b i))) := by
  let C : ∀ i, Classes (b i) :=
    fun i => Classical.choice (classes_exist (b i) (H i).positive (H i).small)
  let n : Fin 4 → ℕ := fun i => Classical.choose (from_preparation (C i) (H i) N)
  have hn (i : Fin 4) := Classical.choose_spec (from_preparation (C i) (H i) N)
  refine ⟨C,n,?_,?_⟩
  · intro i
    exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.1,(hn i).2.2.2.1,
      (hn i).2.2.2.2.1,(hn i).2.2.2.2.2.1,(hn i).2.2.2.2.2.2.1⟩
  · intro hinf hinft
    exact ⟨fun i => Classical.choice ((hn i).2.2.2.2.2.2.2 (hinf i) (hinft i))⟩

end ActualPreparedDescentInterface318
