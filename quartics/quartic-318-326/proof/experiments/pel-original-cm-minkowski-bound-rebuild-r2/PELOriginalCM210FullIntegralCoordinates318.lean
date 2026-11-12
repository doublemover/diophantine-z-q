module
public import PELOriginalCM210DenominatorCongruences318
public section
noncomputable section
namespace PELOriginalCM210FullIntegralCoordinates318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210IntegralTraceData318
lemma integer_coordinates (z:K) (hz:IsIntegral ℤ z) :
    ∃r s:ℤ,z.re=(r:ℚ) ∧ z.im=(s:ℚ) := by
  obtain ⟨T,U,N,hT,hU,hN,h⟩ := denominator_identity z hz
  obtain ⟨h2,h420⟩ := PELOriginalCM210DenominatorCongruences318.denominators T U N h
  obtain ⟨r,hr⟩ := h2
  obtain ⟨s,hs⟩ := h420
  refine ⟨r,s,?_,?_⟩
  · have hh : (T:ℚ)=2*(r:ℚ) := by exact_mod_cast hr
    linarith
  · have hh : (U:ℚ)=420*(s:ℚ) := by exact_mod_cast hs
    linarith
lemma integral_iff_image (z:K) : IsIntegral ℤ z ↔ ∃r:R,intMap r=z := by
  constructor
  · intro hz
    obtain ⟨r,s,hr,hs⟩ := integer_coordinates z hz
    exact ⟨⟨r,s⟩,QuadraticAlgebra.ext hr.symm hs.symm⟩
  · rintro ⟨r,rfl⟩
    exact image_integral r

end PELOriginalCM210FullIntegralCoordinates318
