module
public import PELQuadraticIntegralInvariants318
public section
noncomputable section
namespace PELQuaternionQuadraticCarrier318
open PELQuaternionAlgebra318 QuaternionAlgebra
set_option maxHeartbeats 1000000

abbrev Quadratic (x : B) := QuadraticAlgebra ℚ (-reducedNorm x) (reducedTrace x)

/-- The literal quadratic equation of the same quaternion. -/
theorem relation (x : B) : x*x=(-reducedNorm x) • (1:B)+reducedTrace x • x := by
  ext <;> simp [reducedNorm,reducedTrace] <;> ring

@[expose] def realization (x : B) : Quadratic x →ₐ[ℚ] B :=
  QuadraticAlgebra.lift ⟨x,relation x⟩

theorem realization_value (x : B) (z : Quadratic x) :
    realization x z=z.re • (1:B)+z.im • x := rfl

theorem realization_generator (x : B) : realization x QuadraticAlgebra.omega=x := by
  rw [realization_value]
  simp [QuadraticAlgebra.omega]

/-- Nonscalarity is checked in the three actual signed quaternion coordinates,
not inferred from the four-dimensional ambient algebra. -/
theorem realization_injective (x : B)
    (hx : x.imI≠0 ∨ x.imJ≠0 ∨ x.imK≠0) : Function.Injective (realization x) := by
  intro z w h
  rw [realization_value,realization_value] at h
  have hr := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  change z.re*1+z.im*x.re=w.re*1+w.im*x.re at hr
  simp only [mul_one] at hr
  change z.re*0+z.im*x.imI=w.re*0+w.im*x.imI at hi
  change z.re*0+z.im*x.imJ=w.re*0+w.im*x.imJ at hj
  change z.re*0+z.im*x.imK=w.re*0+w.im*x.imK at hk
  simp only [mul_zero,zero_add] at hi hj hk
  have him : z.im=w.im := by
    rcases hx with hx|hx|hx
    · exact mul_right_cancel₀ hx hi
    · exact mul_right_cancel₀ hx hj
    · exact mul_right_cancel₀ hx hk
  have hre : z.re=w.re := by rw [him] at hr; linarith
  exact QuadraticAlgebra.ext hre him

/-- Integrality is reflected through the actual injective quadratic map;
no assumption on an abstract quadratic field is supplied. -/
theorem generator_integral (x : B)
    (hx : x.imI≠0 ∨ x.imJ≠0 ∨ x.imK≠0) (hint : IsIntegral ℤ x) :
    IsIntegral ℤ (QuadraticAlgebra.omega : Quadratic x) := by
  apply (isIntegral_algHom_iff ((realization x).restrictScalars ℤ)
    (realization_injective x hx)).mp
  change IsIntegral ℤ (realization x QuadraticAlgebra.omega)
  rw [realization_generator]
  exact hint
end PELQuaternionQuadraticCarrier318
