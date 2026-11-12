module
public import ActualTwoDescentInfinitePrimaryDivisible318
public section
noncomputable section
namespace ActualTwoDescentCompatiblePrimaryHalves318
set_option maxHeartbeats 16000000

variable {G : Type*} [CommGroup G]

/-- Actual compatible successive square roots, selected only after square-map surjectivity is proved. -/
def halfTower (hs : Function.Surjective (powMonoidHom (α:=G) 2)) (x : G) : ℕ → G
  | 0 => x
  | k+1 => Classical.choose (hs (halfTower hs x k))

lemma actual_half_tower_step (hs : Function.Surjective (powMonoidHom (α:=G) 2)) (x : G) (k : ℕ) :
    (halfTower hs x (k+1))^2=halfTower hs x k := Classical.choose_spec (hs (halfTower hs x k))

lemma actual_half_tower_power (hs : Function.Surjective (powMonoidHom (α:=G) 2)) (x : G) (k : ℕ) :
    (halfTower hs x k)^(2^k)=x := by
  induction k with
  | zero => simp [halfTower]
  | succ k ih =>
    rw [pow_succ,Nat.mul_comm (2^k) 2,pow_mul,actual_half_tower_step,ih]

end ActualTwoDescentCompatiblePrimaryHalves318
