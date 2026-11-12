module
public import PELOriginalCM210IntegralConjugation318
public section
noncomputable section
namespace PELOriginalCM210IntegralTraceData318
open PELOriginalCM210IntegralConjugation318
lemma trace_integer (z:K) (hz:IsIntegral ℤ z) : ∃T:ℤ,2*z.re=(T:ℚ) := by
  simpa [QuadraticAlgebra.trace_def,PELInertiaNormalizerData318.discriminant]
    using PELQuadraticIntegralInvariants318.trace_integral (-210) 0 z hz
lemma norm_integer (z:K) (hz:IsIntegral ℤ z) :
    ∃N:ℤ,z.re^2+210*z.im^2=(N:ℚ) := by
  obtain ⟨N,hN⟩ := PELQuadraticIntegralInvariants318.norm_integral (-210) 0 z hz
  refine ⟨N,?_⟩
  calc
    z.re^2+210*z.im^2=QuadraticAlgebra.norm z := by
      simp only [QuadraticAlgebra.norm_def]
      change z.re^2+210*z.im^2=z.re*z.re+0*z.re*z.im-(-210)*z.im*z.im
      ring
    _=(N:ℚ) := hN
lemma second_trace_integer (z:K) (hz:IsIntegral ℤ z) :
    ∃U:ℤ,420*z.im=(U:ℚ) := by
  obtain ⟨U,hU⟩ := trace_integer (thetaK*z) (theta_integral.mul hz)
  refine ⟨-U,?_⟩
  simp [thetaK,QuadraticAlgebra.omega,QuadraticAlgebra.re_mul,
    PELInertiaNormalizerData318.discriminant] at hU
  push_cast
  linarith
lemma denominator_identity (z:K) (hz:IsIntegral ℤ z) :
    ∃T U N:ℤ,2*z.re=(T:ℚ) ∧ 420*z.im=(U:ℚ) ∧
      z.re^2+210*z.im^2=(N:ℚ) ∧ 210*T^2+U^2=840*N := by
  obtain ⟨T,hT⟩ := trace_integer z hz
  obtain ⟨U,hU⟩ := second_trace_integer z hz
  obtain ⟨N,hN⟩ := norm_integer z hz
  refine ⟨T,U,N,hT,hU,hN,?_⟩
  have hQ : (210:ℚ)*T^2+U^2=840*N := by
    rw [←hT,←hU,←hN]
    ring
  exact_mod_cast hQ

end PELOriginalCM210IntegralTraceData318
