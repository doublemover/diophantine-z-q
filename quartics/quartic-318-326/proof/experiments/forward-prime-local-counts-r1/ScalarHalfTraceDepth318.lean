module
public import ScalarIndexValuations318
public section
noncomputable section
namespace ScalarHalfTraceDepth318
open ConcreteG8Domain (K)
open GeneratorScalarProgression318 ScalarTranslatedIndex318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma half_trace (u : K) : (u^2).re=u.re^2+2*u.im^2 := by
  norm_num [pow_two]
  ring

/-- At2 the opposite parities of the two terms prevent cancellation for
both the quadratic norm and actual half-trace. Zero coefficients are retained. -/
lemma half_trace_two (u : K) (hn : normCoefficient u≠0) :
    padicValRat 2 ((u^2).re)=padicValRat 2 (normCoefficient u) := by
  by_cases ha : u.re=0
  · simp [half_trace,normCoefficient,ha]
  by_cases hb : u.im=0
  · simp [half_trace,normCoefficient,hb]
  have hf := ScalarPackedLocalUnit318.half_trace_ne u hn
  rw [half_trace] at hf
  have hterm : padicValRat 2 (2*u.im^2)=1+2*padicValRat 2 u.im := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ hb),padicValRat.pow,
      padicValRat.self (by norm_num)]
    norm_num
  have hsum := padicValRat.add_eq_min hf (pow_ne_zero _ ha)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hb))
    (by rw [padicValRat.pow,hterm]; norm_num; omega)
  have hnorm : padicValRat 2 (normCoefficient u)=
      min (2*padicValRat 2 u.re) (1+2*padicValRat 2 u.im) := by
    simpa only [norm_coefficient] using AnchorNorm318.norm_two_value u.re u.im ha hb
  rw [half_trace,hsum,padicValRat.pow,hterm,hnorm]
  norm_num

/-- At3 the inert norm equals twice the minimum coefficient depth; the
actual half-trace has at least that depth, including possible cancellation. -/
lemma half_trace_three (u : K) (hn : normCoefficient u≠0) :
    padicValRat 3 (normCoefficient u)≤padicValRat 3 ((u^2).re) := by
  by_cases ha : u.re=0
  · simp [half_trace,normCoefficient,ha]
  by_cases hb : u.im=0
  · simp [half_trace,normCoefficient,hb]
  have hf := ScalarPackedLocalUnit318.half_trace_ne u hn
  rw [half_trace] at hf
  have htwo : padicValRat 3 (2:ℚ)=0 := by
    simpa using AnchorNorm318.rational_unit_value 3 2 1 (by norm_num) (by norm_num)
  have hterm : padicValRat 3 (2*u.im^2)=2*padicValRat 3 u.im := by
    rw [padicValRat.mul (by norm_num) (pow_ne_zero _ hb),padicValRat.pow,htwo]
    norm_num
  have hsum := padicValRat.min_le_padicValRat_add (p:=3) hf
  rw [padicValRat.pow,hterm] at hsum
  have hnorm : padicValRat 3 (normCoefficient u)=2*min (padicValRat 3 u.re) (padicValRat 3 u.im) := by
    simpa only [norm_coefficient] using AnchorNorm318.norm_three_value u.re u.im ha hb
  rw [half_trace,hnorm]
  omega

end ScalarHalfTraceDepth318
