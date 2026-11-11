module
public import TensorCoefficientDuality318
public import QuadraticPresentation318
public section
noncomputable section
namespace QuadraticIntegralDuality318
open Module QuadraticPresentation318 TensorCoefficientDuality318
set_option maxHeartbeats 1400000
variable {R : Type*} [CommRing R] (a : R)
@[expose] def switch : Fin 2 → Fin 2 := ![1,0]
theorem switch_involutive : Function.Involutive switch := by intro i; fin_cases i <;> rfl

@[expose] def quadraticFrame : Frame R (QuadraticAlgebra R a 0) (Fin 2) where
  basis := QuadraticAlgebra.basis a 0
  switch := switch
  involutive := switch_involutive
  coefficient := QuadraticAlgebra.imₗ a 0
  pairing := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [switch,QuadraticAlgebra.imₗ,QuadraticAlgebra.omega_mul_omega_eq_add]

@[expose] def rootCoefficient : RootRing a →ₗ[R] R :=
  (QuadraticAlgebra.imₗ a 0).comp (presentationEquiv a).symm.toLinearMap

/-- Perfect integral duality for the ACTUAL monic quotient X²-a. The
coefficient functional is the literal root coefficient, even in char2. -/
@[expose] def rootFrame : Frame R (RootRing a) (Fin 2) where
  basis := (QuadraticAlgebra.basis a 0).map (presentationEquiv a).toLinearEquiv
  switch := switch
  involutive := switch_involutive
  coefficient := rootCoefficient a
  pairing := by
    intro i j
    simp only [Basis.map_apply,AlgEquiv.toLinearEquiv_apply,rootCoefficient,LinearMap.comp_apply,
      AlgEquiv.toLinearMap_apply,map_mul,AlgEquiv.symm_apply_apply]
    exact (quadraticFrame a).pairing i j

theorem rootCoefficient_one : rootCoefficient a 1=0 := by
  simp [rootCoefficient,QuadraticAlgebra.imₗ]
theorem rootCoefficient_root : rootCoefficient a (AdjoinRoot.root (polynomial a))=1 := by
  change QuadraticAlgebra.imₗ a 0 ((presentationEquiv a).symm (AdjoinRoot.root (polynomial a)))=1
  rw [←presentationEquiv_generator,AlgEquiv.symm_apply_apply]
  rfl

theorem root_duality (x y : RootRing a) : (rootFrame a).duality x y=rootCoefficient a (x*y) := rfl
end QuadraticIntegralDuality318
