module
public import ScalarPolePreparation318
public section
noncomputable section
namespace ScalarPackedLocalUnit318
open CircuitReplay ScalarForwardWitness318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0

/-- Adding a strictly small local quantity to a genuine unit preserves its
nonvanishing and value. No value is silently assigned to a zero summand. -/
lemma unit_add_small (p : ℕ) [Fact p.Prime] (A B : ℚ)
    (hA : A≠0) (hu : padicValRat p A=0) (hs : 0<padicValRat p B) :
    A+B≠0 ∧ padicValRat p (A+B)=0 := by
  have hB : B≠0 := by intro hz; simp [hz] at hs
  have hsum : A+B≠0 := by
    intro hz
    have hb : B= -A := by linarith
    rw [hb,padicValRat.neg,hu] at hs
    omega
  refine ⟨hsum,?_⟩
  rw [padicValRat.add_eq_of_lt hsum hA hB (by omega),hu]

/-- These inequalities are precisely at the actual packed scalar leaves.
The last inequality retains29*v(r), coming from r*Q² with Q=I/(H*r^15).
They suffice to produce the unit W required by square-denominator preparation. -/
theorem packed_unit (p : ℕ) [Fact p.Prime] (r f H I : ℚ)
    (hr : r≠0) (hf : f≠0) (hH : H≠0) (hI : I≠0)
    (hHdeep : padicValRat p r<padicValRat p H)
    (hfdeep : padicValRat p r<padicValRat p (2*f))
    (hIdeep : 2*padicValRat p H+29*padicValRat p r<2*padicValRat p I) :
    let N := 1+(H/r)^2+2*f/r
    let Q := I/(H*r^15)
    N^2+r*Q^2≠0 ∧ padicValRat p (N^2+r*Q^2)=0 := by
  have hs₁ : 0<padicValRat p ((H/r)^2) := by
    rw [padicValRat.pow,padicValRat.div hH hr]
    norm_num
    omega
  have hs₂ : 0<padicValRat p (2*f/r) := by
    rw [padicValRat.div (mul_ne_zero (by norm_num) hf) hr]
    omega
  obtain ⟨hN₁,hN₁val⟩ := unit_add_small p 1 ((H/r)^2) (by norm_num) (by simp) hs₁
  obtain ⟨hN,hNval⟩ := unit_add_small p (1+(H/r)^2) (2*f/r) hN₁ hN₁val hs₂
  have hQ : I/(H*r^15)≠0 := div_ne_zero hI (mul_ne_zero hH (pow_ne_zero _ hr))
  have hs₃ : 0<padicValRat p (r*(I/(H*r^15))^2) := by
    rw [padicValRat.mul hr (pow_ne_zero _ hQ),padicValRat.pow,
      padicValRat.div hI (mul_ne_zero hH (pow_ne_zero _ hr)),
      padicValRat.mul hH (pow_ne_zero _ hr),padicValRat.pow]
    norm_num
    omega
  exact unit_add_small p ((1+(H/r)^2+2*f/r)^2) (r*(I/(H*r^15))^2)
    (pow_ne_zero _ hN) (by rw [padicValRat.pow,hNval]; simp) hs₃

/-- A single actual-leaf criterion produces the unit condition at every
prime needed by the source scalar normalization. This is not a proof that
the original elliptic-index preparation realizes the inequalities. -/
theorem actual_unit (p : ℕ) [Fact p.Prime] (w : Assignment) (n : ℤ)
    (hr : inputR (w 0)≠0) (hf : w 33≠0) (hH : w 37≠0)
    (hn : n≠0) (hn1 : n≠1)
    (hHdeep : padicValRat p (inputR (w 0))<padicValRat p (w 37))
    (hfdeep : padicValRat p (inputR (w 0))<padicValRat p (2*w 33))
    (hIdeep : 2*padicValRat p (w 37)+29*padicValRat p (inputR (w 0))<
      2*padicValRat p (ActualScalarRoot318.inverseNorm n)) :
    W w n≠0 ∧ padicValRat p (W w n)=0 := by
  have hI : ActualScalarRoot318.inverseNorm n≠0 :=
    inv_ne_zero (ActualScalarRoot318.norm_ne n hn hn1)
  exact packed_unit p (inputR (w 0)) (w 33) (w 37)
    (ActualScalarRoot318.inverseNorm n) hr hf hH hI hHdeep hfdeep hIdeep

lemma half_trace_ne (u : ConcreteG8Domain.K)
    (hn : GeneratorScalarProgression318.normCoefficient u≠0) : (u^2).re≠0 := by
  intro hz
  have he : u.re^2+2*u.im^2=0 := by
    norm_num [pow_two] at hz
    nlinarith [hz]
  apply hn
  unfold GeneratorScalarProgression318.normCoefficient
  nlinarith [sq_nonneg u.re,sq_nonneg u.im]

/-- The exact actual input conditions now imply a square reduced denominator
without assuming the packed-unit conclusion itself. -/
theorem actual_square_denominator (w : Assignment) (n a : ℤ) (hin : w 0=(a:ℚ))
    (hf : w 33≠0) (hH : w 37≠0) (hn : n≠0) (hn1 : n≠1) (hW : W w n≠0)
    (hprep : ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (w 0)) →
      padicValRat p (inputR (w 0))<padicValRat p (w 37) ∧
      padicValRat p (inputR (w 0))<padicValRat p (2*w 33) ∧
      2*padicValRat p (w 37)+29*padicValRat p (inputR (w 0))<
        2*padicValRat p (ActualScalarRoot318.inverseNorm n)) :
    IsSquare (poleInput w n).den := by
  apply ScalarPolePreparation318.actual_square_denominator w n a hin hW
  intro p hp hs
  letI : Fact p.Prime := ⟨hp⟩
  have hr : inputR (w 0)≠0 := by
    have he := integer_inputR_large a
    rw [←hin] at he
    linarith
  obtain ⟨h₁,h₂,h₃⟩ := hprep p hp hs
  exact (actual_unit p w n hr hf hH hn hn1 h₁ h₂ h₃).2

end ScalarPackedLocalUnit318
