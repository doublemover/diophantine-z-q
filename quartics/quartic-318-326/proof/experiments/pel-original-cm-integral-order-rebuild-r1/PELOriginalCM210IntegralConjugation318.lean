module
public import PELInertiaQuadraticEmbeddings318
public import PELQuadraticIntegralInvariants318
public import Mathlib.NumberTheory.NumberField.Basic
public section
noncomputable section
namespace PELOriginalCM210IntegralConjugation318
/-- The SAME original inertia carrier at the original m=210 index. -/
abbrev K := PELInertiaQuadraticEmbeddings318.Quadratic 4
abbrev R := QuadraticAlgebra ℤ (-210) 0
@[expose] def thetaK : K := QuadraticAlgebra.omega
@[expose] def thetaR : R := QuadraticAlgebra.omega
instance : NumberField K where
@[expose] def intMap : R→+*K :=
  QuadraticAlgebra.mapRingHom (Int.castRingHom ℚ) (-210) 0
lemma intMap_coordinates (z:R) : intMap z=⟨(z.re:ℚ),(z.im:ℚ)⟩ := rfl
lemma intMap_injective : Function.Injective intMap := by
  intro z w h
  apply QuadraticAlgebra.ext
  · exact_mod_cast congrArg QuadraticAlgebra.re h
  · exact_mod_cast congrArg QuadraticAlgebra.im h
lemma image_integral (z:R) : IsIntegral ℤ (intMap z) :=
  map_isIntegral_int intMap (IsIntegral.of_finite ℤ z)
lemma theta_integral : IsIntegral ℤ thetaK := by
  simpa [intMap,thetaK,thetaR] using image_integral thetaR
lemma theta_square : thetaK^2=(-210:K) := by
  simp [thetaK,QuadraticAlgebra.omega_pow_two_eq_add,
    PELInertiaNormalizerData318.discriminant,Algebra.smul_def]
lemma original_generator : PELInertiaQuadraticEmbeddings318.realization 4 thetaK=
    PELInertiaNormalizerData318.element 4 :=
  PELInertiaQuadraticEmbeddings318.realization_generator 4
lemma original_integer_image (z:R) :
    PELInertiaQuadraticEmbeddings318.realization 4 (intMap z)=
      (z.re:ℚ) • (1:PELQuaternionAlgebra318.B)+
      (z.im:ℚ) • PELInertiaNormalizerData318.element 4 := rfl

end PELOriginalCM210IntegralConjugation318
