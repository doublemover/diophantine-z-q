module
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Field.ZMod
public section
noncomputable section
namespace F3PairIndependence318
variable {V:Type*} [AddCommGroup V] [Module (ZMod 3) V]
lemma scalar_cases (a:ZMod 3) : a=0 ∨ a=1 ∨ a= -1 := by
  have h:∀a:ZMod 3,a=0 ∨ a=1 ∨ a= -1:=by decide
  exact h a
/-- Independence uses the actual additive structure, not eight arbitrary labels. -/
theorem pair_iff (p q:V) : LinearIndependent (ZMod 3) ![p,q] ↔
    p≠0 ∧ q≠0 ∧ q≠p ∧ q≠ -p := by
  constructor
  · intro h
    have hp:p≠0:=by simpa using h.ne_zero (0:Fin 2)
    have hh:∀a:ZMod 3,a • p≠q:=(LinearIndependent.pair_iff' (K:=ZMod 3) (y:=q) hp).mp h
    refine ⟨hp,?_,?_,?_⟩
    · simpa only [zero_smul,ne_eq,eq_comm] using hh 0
    · simpa only [one_smul,ne_eq,eq_comm] using hh 1
    · simpa only [neg_one_smul,ne_eq,eq_comm] using hh (-1)
  · rintro ⟨hp,hq,hqp,hqn⟩
    apply (LinearIndependent.pair_iff' (K:=ZMod 3) (y:=q) hp).mpr
    intro a
    rcases scalar_cases a with rfl|rfl|rfl
    · simpa only [zero_smul,ne_eq,eq_comm] using hq
    · simpa only [one_smul,ne_eq,eq_comm] using hqp
    · simpa only [neg_one_smul,ne_eq,eq_comm] using hqn
/-- The four actual nonzero combinations cutting out ordered independent pairs. -/
theorem combinations_iff (p q:V) : LinearIndependent (ZMod 3) ![p,q] ↔
    p≠0 ∧ q≠0 ∧ q-p≠0 ∧ q+p≠0 := by
  simp only [pair_iff,ne_eq,sub_eq_zero,add_eq_zero_iff_eq_neg]
end F3PairIndependence318
