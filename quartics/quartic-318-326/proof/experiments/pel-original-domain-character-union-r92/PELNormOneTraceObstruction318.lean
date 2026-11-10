module
public import PELInertiaArithmeticFixedPoints318
public section
noncomputable section
namespace PELNormOneTraceObstruction318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1400000

@[expose] def integralTrace (a : Coordinates) : ℤ := 2*a 0+a 2
@[expose] def integralNorm (a : Coordinates) : ℤ :=
  a 0^2+a 0*a 2+210*a 1^2+210*a 1*a 3-a 2^2+42*a 3^2

theorem original_trace (a : Coordinates) : reducedTrace (embed a)=(integralTrace a:ℚ) := by
  simp only [reducedTrace,embed,integralTrace]
  push_cast
  ring

theorem original_norm (a : Coordinates) : reducedNorm (embed a)=(integralNorm a:ℚ) := by
  simp only [reducedNorm,embed,integralNorm]
  push_cast
  ring

theorem discriminant_identity (a : Coordinates) :
    integralTrace a^2-4*integralNorm a=
      5*a 2^2-840*a 1^2-840*a 1*a 3-168*a 3^2 := by
  unfold integralTrace integralNorm
  ring

lemma mod_five_obstruction (x : ZMod 5) : 2*x^2≠1 := by
  fin_cases x <;> norm_num
lemma mod_seven_obstruction (x : ZMod 7) : 5*x^2≠4 := by
  fin_cases x <;> norm_num

/-- The trace-zero elliptic possibility is excluded in the SAME original
order by its exact norm form at five, not by a classification assumption. -/
theorem trace_ne_zero (a : Coordinates) (hn : integralNorm a=1) : integralTrace a≠0 := by
  intro ht
  have he := discriminant_identity a
  rw [hn,ht] at he
  have hm := congrArg (Int.castRingHom (ZMod 5)) he
  have hz : 2*(a 3:ZMod 5)^2=1 := by
    norm_num at hm ⊢
    linear_combination -hm
  exact mod_five_obstruction _ hz

/-- Both trace-one elliptic possibilities are excluded at seven. -/
theorem trace_sq_ne_one (a : Coordinates) (hn : integralNorm a=1) : integralTrace a^2≠1 := by
  intro ht
  have he := discriminant_identity a
  rw [hn,ht] at he
  have hm := congrArg (Int.castRingHom (ZMod 7)) he
  have hz : 5*(a 2:ZMod 7)^2=4 := by
    norm_num at hm ⊢
    linear_combination -hm
  exact mod_seven_obstruction _ hz

/-- Every norm-one original integral quaternion with real elliptic trace
bound has trace plus or minus two. -/
theorem extreme_trace (x : order) (hn : reducedNorm (x:B)=1)
    (hb : (reducedTrace (x:B):ℝ)^2≤4) :
    reducedTrace (x:B)=2 ∨ reducedTrace (x:B)= -2 := by
  obtain ⟨a,ha⟩ := x.property
  have hnZ : integralNorm a=1 := by
    rw [←ha,original_norm] at hn
    exact_mod_cast hn
  have hbZ : integralTrace a^2≤4 := by
    rw [←ha,original_trace] at hb
    exact_mod_cast hb
  have hlow : -2≤integralTrace a := by nlinarith
  have hupp : integralTrace a≤2 := by nlinarith
  have hn0 := trace_ne_zero a hnZ
  have hn1 := trace_sq_ne_one a hnZ
  have hp : integralTrace a≠1 := by
    intro h
    apply hn1
    rw [h]
    norm_num
  have hm : integralTrace a≠ -1 := by
    intro h
    apply hn1
    rw [h]
    norm_num
  have ht : integralTrace a=2 ∨ integralTrace a= -2 := by
    omega
  rw [←ha,original_trace]
  rcases ht with ht | ht
  · left; exact_mod_cast ht
  · right; exact_mod_cast ht
end PELNormOneTraceObstruction318
