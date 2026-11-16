module
public import ActualTwoDescentRankOnePrimaryEquivalence318
public import Mathlib.Topology.Instances.AddCircle.Defs
public section
noncomputable section
namespace ActualTwoDescentDyadicPrueferModel318
set_option maxHeartbeats 16000000

/-- The standard dyadic Prüfer group, literally the2-primary subgroup of Q/Z. -/
abbrev PrueferTwo := CommGroup.primaryComponent (Multiplicative (AddCircle (1 : ℚ))) 2

def dyadicCircle (k : ℕ) : AddCircle (1 : ℚ) := ((1 : ℚ)/(2^(k+1) : ℕ) : ℚ)

lemma actual_dyadic_circle_order (k : ℕ) : addOrderOf (dyadicCircle k)=2^(k+1) := by
  letI : Fact (0<(1 : ℚ)) := ⟨by norm_num⟩
  exact AddCircle.addOrderOf_period_div (p:=(1 : ℚ)) (pow_pos (by decide) (k+1))

def dyadicGenerator (k : ℕ) : PrueferTwo := ⟨Multiplicative.ofAdd (dyadicCircle k),k+1,by
  change (2^(k+1)) • dyadicCircle k=0
  rw [←actual_dyadic_circle_order]
  exact addOrderOf_nsmul_eq_zero _⟩

lemma actual_dyadic_generator_order (k : ℕ) : orderOf (dyadicGenerator k)=2^(k+1) := by
  rw [←orderOf_injective (PrueferTwo.subtype) Subtype.val_injective (dyadicGenerator k)]
  exact actual_dyadic_circle_order k

lemma actual_dyadic_generator_injective : Function.Injective dyadicGenerator := by
  intro i j h
  have ho := congrArg orderOf h
  rw [actual_dyadic_generator_order,actual_dyadic_generator_order] at ho
  have := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) ho
  omega

lemma actual_pruefer_infinite : Infinite PrueferTwo :=
  Infinite.of_injective dyadicGenerator actual_dyadic_generator_injective

lemma actual_pruefer_is_two_group : IsPGroup 2 PrueferTwo := CommGroup.primaryComponent.isPGroup

end ActualTwoDescentDyadicPrueferModel318
