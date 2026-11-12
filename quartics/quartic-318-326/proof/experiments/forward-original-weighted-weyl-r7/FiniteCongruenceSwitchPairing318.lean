module
public import ActualIntegerRepresentativeCongruence318
public section
noncomputable section
namespace FiniteCongruenceSwitchPairing318
set_option maxHeartbeats 22000000

/-- An actual involution switching the actual congruence predicate
pairs every failed class with exactly one successful ORIGINAL class. -/
@[expose] def switchEquiv {X : Type*} (P : X → Prop) (T : X → X)
    (hT : Function.Involutive T) (hP : ∀x,P (T x)↔¬P x) : X ≃ ({x // P x}×Bool) := by
  classical
  refine {
    toFun := fun x => if h : P x then (⟨x,h⟩,false) else (⟨T x,(hP x).mpr h⟩,true)
    invFun := fun y => if y.2 then T y.1.1 else y.1.1
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    by_cases hx : P x
    · simp only [dif_pos hx,Bool.false_eq_true,if_false]
    · simp only [dif_neg hx,if_true,hT]
  · rintro ⟨y,b⟩
    cases b
    · simp only [Bool.false_eq_true,if_false,dif_pos y.2]
    · have hn : ¬P (T y.1) := by
        intro hh
        exact (hP y.1).mp hh y.2
      simp only [if_true,dif_neg hn,hT]

/-- Cardinal equality retains both the actual source and its actual
successful subspace. No half-density assumption is inserted. -/
theorem actual_half_card {X : Type*} [Fintype X] (P : X → Prop) (T : X → X)
    (hT : Function.Involutive T) (hP : ∀x,P (T x)↔¬P x) :
    Nat.card X=Nat.card {x // P x}*2 := by
  classical
  rw [Nat.card_congr (switchEquiv P T hT hP),Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool]

end FiniteCongruenceSwitchPairing318
