module
public import GaussianIndexPreparation318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.Fintype.BigOperators
public section
noncomputable section
namespace FiniteCurveCharacterCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def Curve (D : F) := {z : F×F // z.2^2=z.1^3-D*z.1}
@[expose] def count (D : F) : ℕ := 1+Nat.card (Curve D)
@[expose] def traceSum (D : F) : ℤ := ∑ x : F, quadraticChar F (x^3-D*x)

/-- The literal affine point carrier, with both coordinates and the exact
curve equation, is equivalent to the disjoint family of ordinate fibers. -/
@[expose] def fiberEquiv (D : F) : Curve D ≃ (Σ x : F, {y : F // y^2=x^3-D*x}) where
  toFun z := ⟨z.1.1,z.1.2,z.2⟩
  invFun z := ⟨(z.1,z.2.1),z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

lemma affine_card (D : F) : Nat.card (Curve D)=∑ x : F, Nat.card {y : F // y^2=x^3-D*x} := by
  classical
  rw [Nat.card_congr (fiberEquiv D)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

lemma fiber_count (hF : ringChar F≠2) (a : F) :
    (Nat.card {y : F // y^2=a}:ℤ)=quadraticChar F a+1 := by
  classical
  simpa only [Set.toFinset_card,Nat.card_eq_fintype_card] using quadraticChar_card_sqrts hF a

/-- Count every actual affine point and infinity, not an abstract group
with a presumed Frobenius trace. -/
theorem count_formula (hF : ringChar F≠2) (D : F) :
    (count D:ℤ)=(Fintype.card F:ℤ)+1+traceSum D := by
  classical
  rw [count,Nat.cast_add,Nat.cast_one,affine_card,Nat.cast_sum]
  simp_rw [fiber_count hF]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,traceSum]
  ring

end FiniteCurveCharacterCount318
