module
public import OriginalCasselsLiteralRangeFinite318
public import Mathlib.Analysis.Real.Sqrt
import all OriginalCasselsDyadicXClass318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsRealLocalCokernel318

open OriginalCasselsLiteralRangeFinite318 OriginalCasselsDyadicXClass318
open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyAddition318
open OriginalCasselsTargetClassChord318 OriginalSelectedCasselsParity318
open ActualTwoDescentSquareClassQuotient318

local instance : DecidableEq ℝ := Classical.decEq _

/-- Every affine real abscissa on the literal quotient is nonnegative:
its other factor is (x−2n)²+12n², strictly positive for n≠0. -/
theorem real_target_x_nonnegative (n x y : ℝ) (hn : n≠0)
    (he : y^2=x*(x^2-4*n*x+16*n^2)) : 0≤x := by
  have hpos : 0<x^2-4*n*x+16*n^2 := by
    rw [show x^2-4*n*x+16*n^2=(x-2*n)^2+12*n^2 by ring]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_ne_zero hn))
  by_contra h
  have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge h) hpos
  rw [←he] at hneg
  exact (not_lt_of_ge (sq_nonneg y)) hneg

theorem real_target_class_one (n : ℝ) (hn : n≠0) (P : TargetPoint n) : targetClass P=1 := by
  cases P with
  | zero => rfl
  | some x y H =>
    by_cases hx : x=0
    · subst x
      simp [targetClass]
    · have he : y^2=x*(x^2-4*n*x+16*n^2) := by
        have h := H.left
        rw [WeierstrassCurve.Affine.equation_iff] at h
        simp only [targetModel,zero_mul,add_zero,zero_add] at h
        linear_combination h
      have hX := real_target_x_nonnegative n x y hn he
      have hs : (Real.sqrt x)^2=x := Real.sq_sqrt hX
      have hs₀ : Real.sqrt x≠0 := by
        intro h
        rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hs
        exact hx hs.symm
      change targetClass (targetPoint n x y hn he)=1
      rw [target_class_at_affine hn hx he,←class_of_one]
      exact (class_of_eq_iff _ _ hx one_ne_zero).2 ⟨Real.sqrt x,hs₀,by rw [one_mul,hs]⟩

/-- Actual real range quotient of the literal point map is the singleton
set, without supposing a real local isogeny or any prior index bound. -/
def realLiteralQuotient (n : ℝ) (hn : n≠0) :
    TargetPoint n ⧸ (literalHom (literal_addition n hn)).range ≃ Unit := by
  let H : TargetPoint n →+ Additive (SquareClass ℝ) :=
    xClassHom (actual_target_class_product n hn)
  let R : AddSubgroup (Additive (SquareClass ℝ)) :=
    AddMonoidHom.range (G := TargetPoint n) (N := Additive (SquareClass ℝ)) H
  let image (P : TargetPoint n) : ↥R := ⟨H P,⟨P,rfl⟩⟩
  let f : Unit → ↥R := fun _ => image 0
  have hF : Function.Bijective f := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · rintro ⟨z,P,rfl⟩
      refine ⟨(),Subtype.ext ?_⟩
      change targetClass (0 : TargetPoint n)=targetClass P
      exact (real_target_class_one n hn 0).trans (real_target_class_one n hn P).symm
  exact (literalQuotientEquiv n hn).toEquiv.trans (Equiv.ofBijective f hF).symm

def localRealIsogeny (n : ℝ) (hn : n≠0) : LocalIsogeny n hn :=
  localIsogeny (literal_addition n hn) (Finite.of_equiv Unit (realLiteralQuotient n hn).symm)

theorem actual_real_cokernel_card (n : ℝ) (hn : n≠0) :
    (localRealIsogeny n hn).cokernelCard=1 := by
  change Nat.card (TargetPoint n ⧸ (literalHom (literal_addition n hn)).range)=1
  rw [Nat.card_congr (realLiteralQuotient n hn),Nat.card_eq_fintype_card] <;> decide

end OriginalCasselsRealLocalCokernel318

#print axioms OriginalCasselsRealLocalCokernel318.real_target_class_one
#print axioms OriginalCasselsRealLocalCokernel318.actual_real_cokernel_card
