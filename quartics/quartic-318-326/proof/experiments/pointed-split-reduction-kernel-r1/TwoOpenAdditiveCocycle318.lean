module
public import AdditiveCocycleRefinement318
public section
noncomputable section
namespace TwoOpenAdditiveCocycle318
open AlgebraicGeometry CategoryTheory Opposite InfinitesimalUnitCocycle318
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (U V : X.Opens)
@[expose] def opens : Bool → X.Opens
  | false => U
  | true => V
lemma cover (h : U ⊔ V = ⊤) : (⊤ : X.Opens) ≤ ⨆ a, opens U V a := by
  rw [← h]
  exact sup_le (le_iSup (opens U V) false) (le_iSup (opens U V) true)
lemma pair_le (a b : Bool) (h : a ≠ b) : opens U V a ⊓ opens U V b ≤ U ⊓ V := by
  cases a <;> cases b <;> simp_all [opens, inf_comm]
lemma restrict_refl (W : X.Opens) (a : Γ(X,W)) : restrict X (show W ≤ W from le_rfl) a = a := by
  change X.presheaf.map (𝟙 (op W)) a = a
  rw [X.presheaf.map_id]
  rfl
/-- One actual overlap section gives complete signed two-open Cech data.
The forward edge is positive; reversal is negative. -/
@[expose] def transition (x : Γ(X,U ⊓ V)) (a b : Bool) : Γ(X,opens U V a ⊓ opens U V b) :=
  if h : a = b then 0 else restrict X (pair_le U V a b h) (if a then -x else x)
@[expose] def cocycle (x : Γ(X,U ⊓ V)) : AdditiveCocycle X (opens U V) where
  transition := transition U V x
  diagonal a := by simp [transition]
  triple a b d := by
    cases a <;> cases b <;> cases d <;>
      simp only [transition, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
        ↓reduceDIte, ↓reduceIte, map_zero, map_neg, restrict_trans,
        zero_add, add_zero, neg_add_cancel, add_neg_cancel]
lemma forward (x : Γ(X,U ⊓ V)) : (cocycle U V x).transition false true = x := by
  change transition U V x false true = x
  simp only [transition, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
  exact restrict_refl _ x
lemma coboundary (x y : Γ(X,U ⊓ V)) (a : Γ(X,U)) (b : Γ(X,V))
    (h : y = restrict X inf_le_left a - restrict X inf_le_right b + x) :
    AdditiveDeformationClasses318.Related X (opens U V) (cocycle U V x) (cocycle U V y) := by
  refine ⟨fun k => match k with | false => a | true => b, ?_⟩
  intro k l
  cases k <;> cases l
  · simp [cocycle, transition]
  · change transition U V y false true = _
    simp only [cocycle, transition, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, restrict_refl]
    exact h
  · change transition U V y true false = _
    simp only [cocycle, transition, Bool.true_eq_false, ↓reduceDIte, ↓reduceIte, map_neg]
    rw [h, map_add, map_sub, restrict_trans, restrict_trans]
    ring
  · simp [cocycle, transition]
end TwoOpenAdditiveCocycle318
