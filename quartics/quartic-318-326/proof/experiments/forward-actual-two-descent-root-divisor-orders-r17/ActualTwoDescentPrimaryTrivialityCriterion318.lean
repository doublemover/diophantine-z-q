module
public import ActualTwoDescentActualShaPrimaryAlternative318
public section
noncomputable section
namespace ActualTwoDescentPrimaryTrivialityCriterion318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318
variable {G : Type*} [CommGroup G]

/-- A genuine2-primary group is trivial exactly when it has no nonidentity2-torsion. -/
lemma actual_primary_trivial_of_two_trivial (hP : IsPGroup 2 G)
    (ht : Subsingleton (powerLevel G 1)) : Subsingleton G := by
  letI := ht
  have h2 (x : G) (hx : x^2=1) : x=1 := by
    let X : powerLevel G 1 := ⟨x,by simpa only [pow_one] using hx⟩
    exact congrArg Subtype.val (Subsingleton.elim X 1)
  have hk : ∀ k (x : G), x^(2^k)=1 → x=1 := by
    intro k
    induction k with
    | zero => intro x hx; simpa only [pow_zero,pow_one] using hx
    | succ k ih =>
      intro x hx
      apply h2 x
      apply ih (x^2)
      rw [←pow_mul,Nat.mul_comm 2 (2^k),←pow_succ]
      exact hx
  constructor
  intro x y
  obtain ⟨k,hx⟩ := isPGroup_iff_pow_pow_eq_one.mp hP x
  obtain ⟨l,hy⟩ := isPGroup_iff_pow_pow_eq_one.mp hP y
  exact (hk k x hx).trans (hk l y hy).symm

end ActualTwoDescentPrimaryTrivialityCriterion318
