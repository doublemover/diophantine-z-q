module
public import LocalizedValuedDualScalar318
public import IntegralClosureDualOrderBaseChange318
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public section
noncomputable section
namespace IntegralClosureNativeDualLocalization318
open CategoryTheory
open scoped TensorProduct
universe u
variable {P Q B : Type u} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)
local instance : Algebra N O := IntegralClosureLocalizationMap318.normalAlgebra
local instance : Module N (N →ₗ[P] P) := ValuedDualPrecomposition318.actionModule P N P
local instance : Module O (O →ₗ[P] Q) := ValuedDualPrecomposition318.actionModule P O Q

/-- Actual scalar-extension object of the OLD finite dual, followed by
the whole normal-order Hom localization and the native localized-base dual. -/
@[expose] def moduleIso [Module.FinitePresentation P N] :
    (ModuleCat.extendScalars i.toRingHom).obj
      (ModuleCat.of N (FiniteDualModuleAction318.Dual P N)) ≅
    ModuleCat.of O (FiniteDualModuleAction318.Dual Q O) :=
  (ModuleCat.extendScalars i.toRingHom).mapIso
    (ValuedDualPrecomposition318.oldDual P N).toModuleIso ≪≫
  (IntegralClosureDualOrderBaseChange318.equivalence (Q:=Q) (B:=B) s).toModuleIso ≪≫
  (LocalizedValuedDualScalar318.equivalence (A:=O) s).toModuleIso

/-- The composite does not merely have the correct target:
its value on each original one-tensor is the original functional value. -/
lemma one_value [Module.FinitePresentation P N]
    (f : FiniteDualModuleAction318.Dual P N) (n : N) :
    (moduleIso (Q:=Q) (B:=B) s).hom (1 ⊗ₜ[N] f) (i n)=algebraMap P Q (f n) := by
  change IntegralClosureDualOrderBaseChange318.equivalence (Q:=Q) (B:=B) s
    (1 ⊗ₜ[N] (f : N →ₗ[P] P)) (i n)=_
  exact IntegralClosureDualOrderBaseChange318.one_value s f n

lemma integral_tensor_value [Module.FinitePresentation P N]
    (f : FiniteDualModuleAction318.Dual P N) (x n : N) :
    (moduleIso (Q:=Q) (B:=B) s).hom (i x ⊗ₜ[N] f) (i n)=
      algebraMap P Q (f (x*n)) := by
  change IntegralClosureDualOrderBaseChange318.equivalence (Q:=Q) (B:=B) s
    (i x ⊗ₜ[N] (f : N →ₗ[P] P)) (i n)=_
  exact IntegralClosureDualOrderBaseChange318.integral_tensor_value s x n f
end IntegralClosureNativeDualLocalization318
