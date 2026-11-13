module
public import PELQuadraticIntegralInvariants318
public import Mathlib.NumberTheory.NumberField.Basic
public section
noncomputable section
namespace PELCMQuadraticIntegralTraceData318
abbrev R (a b:ℤ) := QuadraticAlgebra ℤ a b
abbrev F (a b:ℤ) := QuadraticAlgebra ℚ (a:ℚ) (b:ℚ)
@[expose] def intMap (a b:ℤ) : R a b→+*F a b :=
  QuadraticAlgebra.mapRingHom (Int.castRingHom ℚ) a b
lemma image_integral (a b:ℤ) (z:R a b) : IsIntegral ℤ (intMap a b z) :=
  map_isIntegral_int (intMap a b) (IsIntegral.of_finite ℤ z)
lemma intMap_injective (a b:ℤ) : Function.Injective (intMap a b) := by
  intro z w h
  apply QuadraticAlgebra.ext
  · exact_mod_cast congrArg QuadraticAlgebra.re h
  · exact_mod_cast congrArg QuadraticAlgebra.im h
lemma omega_integral (a b:ℤ) :
    IsIntegral ℤ (QuadraticAlgebra.omega:F a b) := by
  simpa [intMap,QuadraticAlgebra.mapRingHom,QuadraticAlgebra.omega] using
    image_integral a b (QuadraticAlgebra.omega:R a b)
lemma trace_integer (a b:ℤ) (z:F a b) (hz:IsIntegral ℤ z) :
    ∃T:ℤ,2*z.re+(b:ℚ)*z.im=(T:ℚ) := by
  simpa [QuadraticAlgebra.trace_def] using
    PELQuadraticIntegralInvariants318.trace_integral (a:ℚ) (b:ℚ) z hz
lemma norm_integer (a b:ℤ) (z:F a b) (hz:IsIntegral ℤ z) :
    ∃N:ℤ,z.re^2+(b:ℚ)*z.re*z.im-(a:ℚ)*z.im^2=(N:ℚ) := by
  obtain ⟨N,hN⟩ := PELQuadraticIntegralInvariants318.norm_integral (a:ℚ) (b:ℚ) z hz
  refine ⟨N,?_⟩
  simpa [QuadraticAlgebra.norm_def,pow_two,mul_assoc] using hN
@[expose] def D (a b:ℤ) : ℤ := 4*a+b^2
lemma denominator_data (a b:ℤ) (z:F a b) (hz:IsIntegral ℤ z) :
    ∃T U N:ℤ,2*z.re+(b:ℚ)*z.im=(T:ℚ) ∧
      (D a b:ℚ)*z.im=(U:ℚ) ∧
      z.re^2+(b:ℚ)*z.re*z.im-(a:ℚ)*z.im^2=(N:ℚ) ∧
      D a b*T^2-U^2=4*D a b*N := by
  obtain ⟨T,hT⟩ := trace_integer a b z hz
  obtain ⟨V,hV⟩ := trace_integer a b (QuadraticAlgebra.omega*z) ((omega_integral a b).mul hz)
  obtain ⟨N,hN⟩ := norm_integer a b z hz
  have hU : (D a b:ℚ)*z.im=((2*V-b*T:ℤ):ℚ) := by
    simp [QuadraticAlgebra.omega,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] at hV
    push_cast
    dsimp [D]
    push_cast
    linear_combination 2*hV-(b:ℚ)*hT
  refine ⟨T,2*V-b*T,N,hT,hU,hN,?_⟩
  have hQ : (D a b:ℚ)*T^2-((2*V-b*T:ℤ):ℚ)^2=4*(D a b:ℚ)*N := by
    rw [←hT,←hU,←hN]
    simp only [D,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_pow]
    ring
  exact_mod_cast hQ
end PELCMQuadraticIntegralTraceData318
