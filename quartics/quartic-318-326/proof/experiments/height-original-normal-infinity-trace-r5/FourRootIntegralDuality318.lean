module
public import QuadraticIntegralDuality318
public import FourRootOrder318
public section
noncomputable section
namespace FourRootIntegralDuality318
open TensorCoefficientDuality318
open scoped TensorProduct
set_option maxHeartbeats 1800000
variable {R : Type*} [CommRing R] (a : Fin 4 → R)
abbrev Index := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The sixteen actual monomials in the SAME original four quadratic
quotients, together with their perfect highest-coefficient pairing. -/
@[expose] def frame : Frame R (FourRootOrder318.Order a) Index :=
  ((QuadraticIntegralDuality318.rootFrame (a 0)).tensor
    (QuadraticIntegralDuality318.rootFrame (a 1))).tensor
      ((QuadraticIntegralDuality318.rootFrame (a 2)).tensor
        (QuadraticIntegralDuality318.rootFrame (a 3)))
@[expose] def coefficient : FourRootOrder318.Order a →ₗ[R] R := (frame a).coefficient
@[expose] def duality : FourRootOrder318.Order a ≃ₗ[R] Module.Dual R (FourRootOrder318.Order a) :=
  (frame a).duality

theorem coefficient_pure
    (x0 : QuadraticPresentation318.RootRing (a 0)) (x1 : QuadraticPresentation318.RootRing (a 1))
    (x2 : QuadraticPresentation318.RootRing (a 2)) (x3 : QuadraticPresentation318.RootRing (a 3)) :
    coefficient a ((x0 ⊗ₜ[R] x1) ⊗ₜ[R] (x2 ⊗ₜ[R] x3))=
      (QuadraticIntegralDuality318.rootCoefficient (a 0) x0*
        QuadraticIntegralDuality318.rootCoefficient (a 1) x1)*
      (QuadraticIntegralDuality318.rootCoefficient (a 2) x2*
        QuadraticIntegralDuality318.rootCoefficient (a 3) x3) := by
  change Frame.tensorCoefficient _ _ ((x0 ⊗ₜ[R] x1) ⊗ₜ[R] (x2 ⊗ₜ[R] x3))=_
  rw [Frame.tensorCoefficient_tmul]
  change Frame.tensorCoefficient _ _ (x0 ⊗ₜ[R] x1)*Frame.tensorCoefficient _ _ (x2 ⊗ₜ[R] x3)=_
  rw [Frame.tensorCoefficient_tmul,Frame.tensorCoefficient_tmul]
  rfl

theorem duality_apply (x y : FourRootOrder318.Order a) : duality a x y=coefficient a (x*y) := rfl

theorem duality_mul (z x y : FourRootOrder318.Order a) : duality a (z*x) y=duality a x (z*y) :=
  (frame a).duality_mul z x y

/-- Every functional on the actual whole rank16 order is uniquely a
multiple of the integral highest-coefficient functional under the actual
multiplication action. This is stronger than abstract R-module rank16. -/
theorem existsUnique_multiplier (f : Module.Dual R (FourRootOrder318.Order a)) :
    ∃! x : FourRootOrder318.Order a,∀ y, f y=coefficient a (x*y) := by
  refine ⟨(duality a).symm f,?_,?_⟩
  · intro y
    exact (congrArg (fun l => l y) ((duality a).apply_symm_apply f)).symm
  · intro x hx
    apply (duality a).injective
    rw [LinearEquiv.apply_symm_apply]
    ext y
    exact (hx y).symm
end FourRootIntegralDuality318
