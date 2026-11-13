module
public import PELCMOddQuadraticDenominators318
public import PELCMQuadraticNativeIntegerOrder318
public section
noncomputable section
namespace PELCMOddQuadraticFullCoordinates318
open PELCMQuadraticIntegralTraceData318 PELCMOddQuadraticDenominators318
lemma integer_coordinates (i:Fin 3) (z:F (coefficient i) 1) (hz:IsIntegral ℤ z) :
    ∃r s:ℤ,z.re=(r:ℚ) ∧ z.im=(s:ℚ) := by
  obtain ⟨T,U,N,hT,hU,hN,h⟩ := denominator_data (coefficient i) 1 z hz
  have he : discriminant i*T^2-U^2=4*discriminant i*N := by
    simpa [D,discriminant] using h
  obtain ⟨r,s,hs,hr⟩ := coordinates i T U N he
  have hd : (discriminant i:ℚ)≠0 := by exact_mod_cast discriminant_nonzero i
  have hsQ : (discriminant i:ℚ)*z.im=(discriminant i:ℚ)*(s:ℚ) := by
    calc
      _=(U:ℚ) := by simpa [D,discriminant] using hU
      _=_ := by exact_mod_cast hs
  have him : z.im=(s:ℚ) := mul_left_cancel₀ hd hsQ
  refine ⟨r,s,?_,him⟩
  have hrQ : (T:ℚ)=2*(r:ℚ)+(s:ℚ) := by exact_mod_cast hr
  norm_num at hT
  rw [him] at hT
  linarith
end PELCMOddQuadraticFullCoordinates318
