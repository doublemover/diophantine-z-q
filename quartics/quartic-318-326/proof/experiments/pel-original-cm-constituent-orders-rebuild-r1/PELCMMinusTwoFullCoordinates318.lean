module
public import PELCMQuadraticIntegralTraceData318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
namespace PELCMMinusTwoFullCoordinates318
open PELCMQuadraticIntegralTraceData318
lemma mod8_obstruction : ∀t u:ZMod 8,2*t^2+u^2=0 →
    ZMod.castHom (by decide:2∣8) (ZMod 2) t=0 ∧
    ZMod.castHom (by decide:4∣8) (ZMod 4) u=0 := by decide
lemma denominators (T U N:ℤ) (h:2*T^2+U^2=8*N) : 2∣T ∧ 4∣U := by
  have hh := congrArg (Int.castRingHom (ZMod 8)) h
  have he : 2*(T:ZMod 8)^2+(U:ZMod 8)^2=0 := by
    norm_num at hh ⊢ <;> exact hh
  have ho := mod8_obstruction (T:ZMod 8) (U:ZMod 8) he
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd T 2).mp (by simpa using ho.1),
    (ZMod.intCast_zmod_eq_zero_iff_dvd U 4).mp (by simpa using ho.2)⟩
lemma integer_coordinates (z:F (-2) 0) (hz:IsIntegral ℤ z) :
    ∃r s:ℤ,z.re=(r:ℚ) ∧ z.im=(s:ℚ) := by
  obtain ⟨T,hT⟩ := trace_integer (-2) 0 z hz
  obtain ⟨V,hV⟩ := trace_integer (-2) 0 (QuadraticAlgebra.omega*z)
    ((omega_integral (-2) 0).mul hz)
  obtain ⟨N,hN⟩ := norm_integer (-2) 0 z hz
  have hU : 4*z.im=(-V:ℚ) := by
    simp [QuadraticAlgebra.omega,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] at hV
    linarith
  have h : 2*T^2+(-V)^2=8*N := by
    have hQ : (2:ℚ)*T^2+(-V:ℚ)^2=8*N := by
      norm_num at hT hN
      rw [←hT,←hU,←hN]
      ring
    exact_mod_cast hQ
  obtain ⟨h2,h4⟩ := denominators T (-V) N h
  obtain ⟨r,hr⟩ := h2
  obtain ⟨s,hs⟩ := h4
  refine ⟨r,s,?_,?_⟩
  · have hrQ : (T:ℚ)=2*(r:ℚ) := by exact_mod_cast hr
    norm_num at hT
    linarith
  · have hsQ : (-V:ℚ)=4*(s:ℚ) := by exact_mod_cast hs
    linarith
end PELCMMinusTwoFullCoordinates318
