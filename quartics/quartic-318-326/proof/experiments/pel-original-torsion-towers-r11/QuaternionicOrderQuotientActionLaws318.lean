module
public import QuaternionicOrderPeriodQuotient318
public import Mathlib.Algebra.Group.Hom.End
public section
noncomputable section
namespace QuaternionicOrderQuotientActionLaws318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
variable {B : Type*} [Ring B] (ρ : B →+* RealMatrices) (O : Subring B) (τ : ℂ)

lemma linear_zero (z : ComplexVectors) : leftLinear (0 : RealMatrices) z=0 := by
  funext i
  simp [leftLinear,action]
lemma linear_one (z : ComplexVectors) : leftLinear (1 : RealMatrices) z=z := by
  funext i
  fin_cases i <;> simp [leftLinear,action]
lemma linear_add (A B : RealMatrices) (z : ComplexVectors) :
    leftLinear (A+B) z=leftLinear A z+leftLinear B z := by
  funext i
  simp [leftLinear,action]
  ring
lemma linear_mul (A B : RealMatrices) (z : ComplexVectors) :
    leftLinear (A*B) z=leftLinear A (leftLinear B z) := by
  funext i
  simp [leftLinear,action,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- Actual order action laws on the quotient by the entire ORIGINAL
period subgroup, proved from the literal matrix action on representatives. -/
lemma zero_action (q : PeriodQuotient ρ O τ) : orderEnd ρ O τ 0 q=0 := by
  refine Quotient.inductionOn q ?_
  intro z
  change QuotientAddGroup.mk' (periodSubgroup ρ O τ) (leftLinear (ρ (0:B)) z)=0
  rw [map_zero,linear_zero,map_zero]
lemma one_action (q : PeriodQuotient ρ O τ) : orderEnd ρ O τ 1 q=q := by
  refine Quotient.inductionOn q ?_
  intro z
  change QuotientAddGroup.mk' (periodSubgroup ρ O τ) (leftLinear (ρ (1:B)) z)=_
  rw [map_one,linear_one]
lemma add_action (a b : O) (q : PeriodQuotient ρ O τ) :
    orderEnd ρ O τ (a+b) q=orderEnd ρ O τ a q+orderEnd ρ O τ b q := by
  refine Quotient.inductionOn q ?_
  intro z
  change QuotientAddGroup.mk' (periodSubgroup ρ O τ) (leftLinear (ρ ((a:B)+b)) z)=_
  rw [map_add,linear_add,map_add]
  rfl
lemma mul_action (a b : O) (q : PeriodQuotient ρ O τ) :
    orderEnd ρ O τ (a*b) q=orderEnd ρ O τ a (orderEnd ρ O τ b q) := by
  refine Quotient.inductionOn q ?_
  intro z
  change QuotientAddGroup.mk' (periodSubgroup ρ O τ) (leftLinear (ρ ((a:B)*b)) z)=_
  rw [map_mul,linear_mul]
  rfl

/-- The same original order, with its noncommutative multiplication,
acts as a genuine ring of additive endomorphisms of its original torus. -/
@[expose] def ringAction : O →+* AddMonoid.End (PeriodQuotient ρ O τ) where
  toFun := orderEnd ρ O τ
  map_zero' := by ext q; exact zero_action ρ O τ q
  map_one' := by ext q; exact one_action ρ O τ q
  map_add' a b := by ext q; exact add_action ρ O τ a b q
  map_mul' a b := by ext q; exact mul_action ρ O τ a b q
end QuaternionicOrderQuotientActionLaws318
