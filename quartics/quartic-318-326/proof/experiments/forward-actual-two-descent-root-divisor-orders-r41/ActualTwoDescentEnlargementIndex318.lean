module
public import ActualTwoDescentSmallProducer318
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Reindex
public section
noncomputable section
namespace ActualTwoDescentEnlargementIndex318
open ActualTwoDescentDiagonalExtension318
set_option maxHeartbeats 16000000

def unitFinOne : Unit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ()
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _

/-- Identify the recursive diagonal-choice index with an ordinary old/new
support sum. The original support embedding is preserved pointwise. -/
def recursiveEquiv (U : Type*) : (n : ℕ) → Index U n ≃ U ⊕ Fin n
  | 0 =>
    { toFun := Sum.inl
      invFun := Sum.elim id Fin.elim0
      left_inv := fun _ => rfl
      right_inv := by
        intro x
        cases x with
        | inl u => rfl
        | inr i => exact Fin.elim0 i }
  | n+1 =>
    ((Equiv.sumCongr (recursiveEquiv U n) (Equiv.refl Unit)).trans
      (Equiv.sumAssoc U (Fin n) Unit)).trans
      (Equiv.sumCongr (Equiv.refl U)
        ((Equiv.sumCongr (Equiv.refl (Fin n)) unitFinOne).trans finSumFinEquiv))

lemma recursiveEquiv_base (U : Type*) (n : ℕ) (u : U) :
    recursiveEquiv U n (baseEmbed U n u)=Sum.inl u := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recursiveEquiv,baseEmbed,ih]

def supportEquiv (U J : Type*) [Fintype J] : Index U (Fintype.card J) ≃ U ⊕ J :=
  (recursiveEquiv U (Fintype.card J)).trans
    (Equiv.sumCongr (Equiv.refl U) (Fintype.equivFin J).symm)

lemma supportEquiv_base (U J : Type*) [Fintype J] (u : U) :
    supportEquiv U J (baseEmbed U (Fintype.card J) u)=Sum.inl u := by
  simp [supportEquiv,recursiveEquiv_base]
lemma supportEquiv_symm_inl (U J : Type*) [Fintype J] (u : U) :
    (supportEquiv U J).symm (Sum.inl u)=baseEmbed U (Fintype.card J) u := by
  apply (supportEquiv U J).injective
  rw [Equiv.apply_symm_apply,supportEquiv_base]

end ActualTwoDescentEnlargementIndex318
