module
public import ActualTwoDescentFinitePrimaryImages318
public section
noncomputable section
namespace ActualTwoDescentAlternatingCyclicPairing318
set_option maxHeartbeats 16000000

variable {G A : Type*} [CommGroup G] [CommGroup A]

/-- Bimultiplicative pairings into ANY abelian target vanish on cyclic groups if alternating. -/
lemma actual_alternating_cyclic_pairing_zero [IsCyclic G]
    (e : G →* (G →* A)) (halt : ∀ x, e x x=1) : ∀ x y, e x y=1 := by
  obtain ⟨g,hg⟩ := exists_zpow_surjective G
  intro x y
  obtain ⟨i,rfl⟩ := hg x
  obtain ⟨j,rfl⟩ := hg y
  rw [map_zpow]
  change (e g (g^j))^i=1
  rw [map_zpow,halt,one_zpow,one_zpow]

/-- Nondegenerate alternating pairing on a cyclic group forces the group trivial. -/
lemma actual_nondegenerate_alternating_cyclic [IsCyclic G]
    (e : G →* (G →* A)) (halt : ∀ x, e x x=1)
    (hnd : ∀ x, (∀ y, e x y=1) → x=1) : Subsingleton G := by
  constructor
  intro x y
  exact (hnd x (actual_alternating_cyclic_pairing_zero e halt x)).trans
    (hnd y (actual_alternating_cyclic_pairing_zero e halt y)).symm

end ActualTwoDescentAlternatingCyclicPairing318
