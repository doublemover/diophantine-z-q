module
public import FiniteDualAdjunction318
public section
noncomputable section
namespace FiniteFrameFunctionalAdjunction318
variable {P A N ι : Type*} [CommRing P] [CommRing A] [Algebra P A]
  [AddCommGroup N] [Module A N] [Module P N] [IsScalarTower P A N]
  [Fintype ι] [DecidableEq ι] (F : TensorCoefficientDuality318.Frame P A ι)

/-- Use the genuine raw-order-linear perfect coefficient frame on the
ENTIRE dual, before invoking coinduction on the larger order. -/
@[expose] def frameHom : (N →ₗ[A] A) ≃ (N →ₗ[A] FiniteDualModuleAction318.Dual P A) where
  toFun f := (FiniteDualModuleAction318.frame P A F).toLinearMap.comp f
  invFun f := (FiniteDualModuleAction318.frame P A F).symm.toLinearMap.comp f
  left_inv f := by
    apply LinearMap.ext
    intro n
    exact (FiniteDualModuleAction318.frame P A F).symm_apply_apply (f n)
  right_inv f := by
    apply LinearMap.ext
    intro n
    exact (FiniteDualModuleAction318.frame P A F).apply_symm_apply (f n)

/-- Every polynomial-base-linear functional, with no finite-free or
projective hypothesis on N, comes from a unique raw-order-linear map. -/
@[expose] def equivalence : (N →ₗ[A] A) ≃ (N →ₗ[P] P) :=
  (frameHom (N:=N) F).trans FiniteDualAdjunction318.homEquiv

lemma evaluate (f : N →ₗ[A] A) (n : N) :
    equivalence F f n=F.coefficient (f n) := by
  change F.coefficient (f n*1)=F.coefficient (f n)
  rw [mul_one]
end FiniteFrameFunctionalAdjunction318
