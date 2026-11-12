module
public import IntegralClosureModuleLocalization318
public import Mathlib.Algebra.Module.FinitePresentation
public section
noncomputable section
namespace IntegralClosureFullDualLocalization318
open scoped TensorProduct
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)
local instance : IsLocalizedModule (Submonoid.powers s) i.toLinearMap :=
  IntegralClosureModuleLocalization318.localization (Q:=Q) (B:=B) s

/-- Extend EVERY old polynomial-linear functional along the actual
normal-order inclusion, with values in the literal localized base. -/
@[expose] def map : (N →ₗ[P] P) →ₗ[P] (O →ₗ[P] Q) :=
  IsLocalizedModule.map (Submonoid.powers s) i.toLinearMap (Algebra.linearMap P Q)

lemma map_value (f : N →ₗ[P] P) (n : N) :
    map (Q:=Q) (B:=B) s f (i n)=algebraMap P Q (f n) :=
  IsLocalizedModule.map_apply (Submonoid.powers s) i.toLinearMap
    (Algebra.linearMap P Q) f n

lemma localization [Module.FinitePresentation P N] :
    IsLocalizedModule (Submonoid.powers s) (map (Q:=Q) (B:=B) s) :=
  Module.FinitePresentation.isLocalizedModule_map
    (Submonoid.powers s) i.toLinearMap (Algebra.linearMap P Q)

lemma baseChange [Module.FinitePresentation P N] :
    IsBaseChange Q (map (Q:=Q) (B:=B) s) := by
  letI := localization (Q:=Q) (B:=B) s
  exact IsLocalizedModule.isBaseChange (Submonoid.powers s) Q (map (Q:=Q) (B:=B) s)

/-- Full Hom localization, not merely a map on a chosen basis.
The target is explicitly P-linear Hom with its Q action on the output. -/
@[expose] def equivalence [Module.FinitePresentation P N] :
    Q ⊗[P] (N →ₗ[P] P) ≃ₗ[Q] (O →ₗ[P] Q) :=
  (baseChange (Q:=Q) (B:=B) s).equiv

lemma one_value [Module.FinitePresentation P N] (f : N →ₗ[P] P) (n : N) :
    equivalence (Q:=Q) (B:=B) s (1 ⊗ₜ[P] f) (i n)=algebraMap P Q (f n) := by
  rw [equivalence,IsBaseChange.equiv_tmul,one_smul,map_value]
end IntegralClosureFullDualLocalization318
