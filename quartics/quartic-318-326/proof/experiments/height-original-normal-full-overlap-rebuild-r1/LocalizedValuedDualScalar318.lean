module
public import ValuedDualPrecomposition318
public import Mathlib.RingTheory.Localization.Module
public section
noncomputable section
namespace LocalizedValuedDualScalar318
variable {P Q A : Type*} [CommRing P] [CommRing Q] [CommRing A]
  [Algebra P Q] [Algebra P A] [Algebra Q A] [IsScalarTower P Q A]
  (s : P) [IsLocalization.Away s Q]
local instance : Module A (A →ₗ[P] Q) := ValuedDualPrecomposition318.actionModule P A Q

/-- Every P-linear valued functional is Q-linear because Q is the actual
localization of P. Both sides have the INPUT multiplication action of A. -/
@[expose] def equivalence : (A →ₗ[P] Q) ≃ₗ[A] FiniteDualModuleAction318.Dual Q A where
  toFun f := f.extendScalarsOfIsLocalization (Submonoid.powers s) Q
  invFun f := f.restrictScalars P
  left_inv f := by apply LinearMap.ext; intro x; rfl
  right_inv f := by apply LinearMap.ext; intro x; rfl
  map_add' f g := by apply LinearMap.ext; intro x; rfl
  map_smul' a f := by apply LinearMap.ext; intro x; rfl

lemma value (f : A →ₗ[P] Q) (a : A) : equivalence s f a=f a := rfl
lemma inverse_value (f : FiniteDualModuleAction318.Dual Q A) (a : A) :
    (equivalence s).symm f a=f a := rfl
end LocalizedValuedDualScalar318
