module
public import FiniteDualAdjunction318
public import OriginalWholeDualityModel318
public section
noncomputable section
namespace NormalizedWholeFiniteDualityAdjunction318
open NormalizedWholeOverlap318 NormalizedWholeDualityFrames318
set_option maxHeartbeats 1600000
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

/-- Actual finite-chart duality for EVERY module over the whole original
order. No local root inversion or smoothness restriction enters the adjunction. -/
@[expose] def finiteAdjunction (M : Type*) [AddCommGroup M]
    [Module (FiniteOrder R d a) M] [Module R[X] M]
    [IsScalarTower R[X] (FiniteOrder R d a) M] :
    (M →ₗ[FiniteOrder R d a] FiniteDual R d a) ≃ (M →ₗ[R[X]] R[X]) :=
  FiniteDualAdjunction318.homEquiv

@[expose] def infinityAdjunction (M : Type*) [AddCommGroup M]
    [Module (InfinityOrder R d a) M] [Module R[X] M]
    [IsScalarTower R[X] (InfinityOrder R d a) M] :
    (M →ₗ[InfinityOrder R d a] InfinityDual R d a) ≃ (M →ₗ[R[X]] R[X]) :=
  FiniteDualAdjunction318.homEquiv

/-- The adjoint counits of the produced finite/infinity frames are the
literal highest-root coefficient functionals already compared on overlap. -/
theorem finite_counit :
    FiniteDualAdjunction318.evaluateOne (finiteFrame R d a).toLinearMap=
      FourRootIntegralDuality318.coefficient (DVRNormalizedFiniteOrder318.coefficient R d a) :=
  FiniteDualAdjunction318.counit_frame _
theorem infinity_counit :
    FiniteDualAdjunction318.evaluateOne (infinityFrame R d a).toLinearMap=
      FourRootIntegralDuality318.coefficient (DVRNormalizedInfinityOrder318.coefficient R d a) :=
  FiniteDualAdjunction318.counit_frame _

/-- Every actual base-linear functional on an arbitrary whole-order
module has a UNIQUE order-linear dual-valued extension with its specified
value at1. This is an affine universal property, not a dimension surrogate. -/
theorem finite_unique (M : Type*) [AddCommGroup M]
    [Module (FiniteOrder R d a) M] [Module R[X] M]
    [IsScalarTower R[X] (FiniteOrder R d a) M] (g : M →ₗ[R[X]] R[X]) :
    ∃! f : M →ₗ[FiniteOrder R d a] FiniteDual R d a,
      FiniteDualAdjunction318.evaluateOne f=g := by
  refine ⟨(finiteAdjunction R d a M).symm g,?_,?_⟩
  · exact (finiteAdjunction R d a M).apply_symm_apply g
  · intro f hf
    apply (finiteAdjunction R d a M).injective
    exact hf.trans ((finiteAdjunction R d a M).apply_symm_apply g).symm

theorem infinity_unique (M : Type*) [AddCommGroup M]
    [Module (InfinityOrder R d a) M] [Module R[X] M]
    [IsScalarTower R[X] (InfinityOrder R d a) M] (g : M →ₗ[R[X]] R[X]) :
    ∃! f : M →ₗ[InfinityOrder R d a] InfinityDual R d a,
      FiniteDualAdjunction318.evaluateOne f=g := by
  refine ⟨(infinityAdjunction R d a M).symm g,?_,?_⟩
  · exact (infinityAdjunction R d a M).apply_symm_apply g
  · intro f hf
    apply (infinityAdjunction R d a M).injective
    exact hf.trans ((infinityAdjunction R d a M).apply_symm_apply g).symm
end NormalizedWholeFiniteDualityAdjunction318
