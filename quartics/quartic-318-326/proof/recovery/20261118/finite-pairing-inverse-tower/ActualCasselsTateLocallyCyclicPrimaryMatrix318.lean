module
public import ActualTwoDescentActualShaHigherLevels318
public import ActualTwoDescentAlternatingCyclicPairing318
public section
noncomputable section
namespace ActualCasselsTateLocallyCyclicPrimaryMatrix318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentAlternatingCyclicPairing318
open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaHigherLevels318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318
variable {P A : Type*} [CommGroup P] [CommGroup A]

private def restrictBoth (D : Subgroup P) (B : P →* (P →* A)) :
    D →* (D →* A) where
  toFun x := (B x.val).comp D.subtype
  map_one' := by ext y; exact congrArg (fun f : P →* A => f y.val) B.map_one
  map_mul' x z := by ext y; exact congrArg (fun f : P →* A => f y.val) (B.map_mul x.val z.val)

/-- No nondegeneracy or identification of radicals is required. Pairwise
cyclicity suffices, even when the whole primary group is infinite and
there is no single cyclic group containing all elements at once. -/
theorem all_entries_one (B : P →* (P →* A)) (ha : ∀ x, B x x=1)
    (hp : IsPGroup 2 P) (hl : ∀ k, IsCyclic (powerLevel P k)) (x y : P) : B x y=1 := by
  obtain ⟨i,hi⟩ := hp x
  obtain ⟨j,hj⟩ := hp y
  let D := powerLevel P (max i j)
  letI : IsCyclic D := hl _
  have hx : x ∈ D := actual_power_level_mono P (Nat.le_max_left i j) hi
  have hy : y ∈ D := actual_power_level_mono P (Nat.le_max_right i j) hj
  exact actual_alternating_cyclic_pairing_zero (restrictBoth D B) (fun u => ha u.val)
    (⟨x,hx⟩ : D) (⟨y,hy⟩ : D)

theorem actual_primary_matrix (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8)
    (B : actualShaPrimary n hn →* (actualShaPrimary n hn →* A))
    (ha : ∀ x, B x x=1) (x y : actualShaPrimary n hn) : B x y = 1 :=
  all_entries_one B ha (actual_sha_primary_is_two_group n hn)
    (fun k => (actual_sha_higher_levels n hn hf hb hS k).2.2) x y
end ActualCasselsTateLocallyCyclicPrimaryMatrix318
