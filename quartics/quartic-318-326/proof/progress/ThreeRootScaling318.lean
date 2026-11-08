module
public import ThreeTorsionFieldPoints318
public section
noncomputable section
namespace ThreeRootScaling318
open Polynomial
set_option maxHeartbeats 0
variable {K : Type*} [Field K] (A B A' B' : K) (s : Kˣ)
  (hA : A'=(s:K)^2*A) (hB : B'=(s:K)^3*B)

include hA hB in
/-- The actual third-division quartic transforms by the fourth power of
the x-coordinate scale, independently of a square-root choice. -/
lemma division_scale (x : K) :
    (ThreeTorsionIdentity318.divisionPolynomial A' B').eval ((s:K)*x)=
      (s:K)^4*(ThreeTorsionIdentity318.divisionPolynomial A B).eval x := by
  simp only [ThreeTorsionIdentity318.divisionPolynomial,eval_sub,eval_add,eval_mul,
    eval_pow,eval_ofNat,eval_X,eval_C,hA,hB]
  ring

include hA hB in
lemma root_scale_iff (x : K) :
    (ThreeTorsionIdentity318.divisionPolynomial A' B').eval ((s:K)*x)=0 ↔
      (ThreeTorsionIdentity318.divisionPolynomial A B).eval x=0 := by
  rw [division_scale A B A' B' s hA hB]
  simp [Units.ne_zero s]

abbrev Roots (a b : K) := {x : K // (ThreeTorsionIdentity318.divisionPolynomial a b).eval x=0}

@[expose] def rootEquiv : Roots A B ≃ Roots A' B' where
  toFun x := ⟨(s:K)*x.val,(root_scale_iff A B A' B' s hA hB x.val).mpr x.property⟩
  invFun x := ⟨x.val/(s:K),(root_scale_iff A B A' B' s hA hB (x.val/(s:K))).mp
    (by simpa [mul_div_cancel₀,Units.ne_zero s] using x.property)⟩
  left_inv x := by apply Subtype.ext; simp [Units.ne_zero s]
  right_inv x := by apply Subtype.ext; simp [mul_div_cancel₀,Units.ne_zero s]

end ThreeRootScaling318
