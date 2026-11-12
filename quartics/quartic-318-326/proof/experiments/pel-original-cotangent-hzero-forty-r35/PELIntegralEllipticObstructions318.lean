module
public import PELPositiveNormalizerNormalForm318
public section
noncomputable section
namespace PELIntegralEllipticObstructions318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELLevelThreeSimilitudes318
set_option maxHeartbeats 2000000

@[expose] def trace (a : Coordinates) : ℤ := 2*a 0+a 2

theorem original_trace (a : Coordinates) : reducedTrace (embed a)=(trace a:ℚ) := by
  simp only [reducedTrace,embed,trace]
  push_cast <;> ring

theorem discriminant_identity (a : Coordinates) :
    trace a^2-4*integralNorm a=5*a 2^2-840*a 1^2-840*a 1*a 3-168*a 3^2 := by
  unfold trace integralNorm
  ring

lemma square_five (x : ZMod 5) : 2*x^2≠1 := by fin_cases x <;> norm_num
lemma square_seven (x : ZMod 7) : 5*x^2≠4 := by fin_cases x <;> norm_num

/-- These two forbidden discriminants concern the ORIGINAL integral order,
not an arbitrary quadratic field substituted for its quaternion carrier. -/
theorem discriminant_ne_neg_four (a : Coordinates) : trace a^2-4*integralNorm a≠ -4 := by
  intro h
  have he := discriminant_identity a
  rw [h] at he
  have hm := congrArg (Int.castRingHom (ZMod 5)) he
  have hz : 2*(a 3:ZMod 5)^2=1 := by
    norm_num at hm ⊢
    linear_combination -hm
  exact square_five _ hz

theorem discriminant_ne_neg_three (a : Coordinates) : trace a^2-4*integralNorm a≠ -3 := by
  intro h
  have he := discriminant_identity a
  rw [h] at he
  have hm := congrArg (Int.castRingHom (ZMod 7)) he
  have hz : 5*(a 2:ZMod 7)^2=4 := by
    norm_num at hm ⊢
    linear_combination -hm
  exact square_seven _ hz

theorem trace_zero_norm (a : Coordinates) (h : trace a=0) :
    integralNorm a= -5*a 0^2+210*a 1^2+210*a 1*a 3+42*a 3^2 := by
  have h2 : a 2= -2*a 0 := by unfold trace at h; linarith
  rw [integralNorm,h2]
  ring

lemma square_three_values (x : ZMod 3) : x^2=0 ∨ x^2=1 := by fin_cases x <;> norm_num
lemma twice_square_five_values (x : ZMod 5) : 2*x^2=0 ∨ 2*x^2=2 ∨ 2*x^2=3 := by
  fin_cases x <;> norm_num
lemma twice_square_seven_values (x : ZMod 7) : 2*x^2=0 ∨ 2*x^2=1 ∨ 2*x^2=2 ∨ 2*x^2=4 := by
  fin_cases x <;> norm_num
lemma ternary_eight (x y z : ZMod 8) : -5*x^2+2*y^2+2*y*z+2*z^2≠7 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num

/-- The actual trace-zero original norm is locally restricted at ALL four
ramified primes. The dyadic condition is included, not inferred from odd primes. -/
theorem trace_zero_residues (a : Coordinates) (h : trace a=0) :
    ((integralNorm a:ZMod 3)=0 ∨ (integralNorm a:ZMod 3)=1) ∧
    ((integralNorm a:ZMod 5)=0 ∨ (integralNorm a:ZMod 5)=2 ∨ (integralNorm a:ZMod 5)=3) ∧
    ((integralNorm a:ZMod 7)=0 ∨ (integralNorm a:ZMod 7)=1 ∨
      (integralNorm a:ZMod 7)=2 ∨ (integralNorm a:ZMod 7)=4) ∧
    (integralNorm a:ZMod 8)≠7 := by
  have he := trace_zero_norm a h
  have h3 : (integralNorm a:ZMod 3)=(a 0:ZMod 3)^2 := by
    have hm := congrArg (Int.castRingHom (ZMod 3)) he
    norm_num at hm ⊢
    linear_combination hm
  have h5 : (integralNorm a:ZMod 5)=2*(a 3:ZMod 5)^2 := by
    have hm := congrArg (Int.castRingHom (ZMod 5)) he
    norm_num at hm ⊢
    linear_combination hm
  have h7 : (integralNorm a:ZMod 7)=2*(a 0:ZMod 7)^2 := by
    have hm := congrArg (Int.castRingHom (ZMod 7)) he
    norm_num at hm ⊢
    linear_combination hm
  have h8 : (integralNorm a:ZMod 8)=
      -5*(a 0:ZMod 8)^2+2*(a 1:ZMod 8)^2+2*(a 1:ZMod 8)*(a 3:ZMod 8)+2*(a 3:ZMod 8)^2 := by
    have hm := congrArg (Int.castRingHom (ZMod 8)) he
    norm_num at hm ⊢
    linear_combination hm
  refine ⟨?_,?_,?_,?_⟩
  · rw [h3]; exact square_three_values _
  · rw [h5]; exact twice_square_five_values _
  · rw [h7]; exact twice_square_seven_values _
  · rw [h8]; exact ternary_eight _ _ _
end PELIntegralEllipticObstructions318
