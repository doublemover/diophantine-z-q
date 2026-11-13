module
public import IntegralClosureDualOrderLinearity318
public section
noncomputable section
namespace IntegralClosureDualOrderBaseChange318
open scoped TensorProduct
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)
local instance : Algebra N O := IntegralClosureLocalizationMap318.normalAlgebra
local instance : IsScalarTower P N O := IntegralClosureLocalizationMap318.baseTower
local instance : Module N (N →ₗ[P] P) := ValuedDualPrecomposition318.actionModule P N P
local instance : Module O (O →ₗ[P] Q) := ValuedDualPrecomposition318.actionModule P O Q
local instance : Module N (O →ₗ[P] Q) := Module.compHom _ i.toRingHom
local instance : IsScalarTower P N (N →ₗ[P] P) := IntegralClosureDualOrderLinearity318.sourceTower
local instance : IsScalarTower P N (O →ₗ[P] Q) := IntegralClosureDualOrderLinearity318.targetBaseTower
local instance : IsScalarTower N O (O →ₗ[P] Q) := IntegralClosureDualOrderLinearity318.targetOrderTower

lemma localization [Module.FinitePresentation P N] :
    IsLocalizedModule (Submonoid.powers (algebraMap P N s))
      (IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s) := by
  letI : IsLocalizedModule (Submonoid.powers s)
      ((IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s).restrictScalars P) := by
    rw [IntegralClosureDualOrderLinearity318.restrictScalars]
    exact IntegralClosureFullDualLocalization318.localization s
  rw [←Algebra.algebraMapSubmonoid_powers]
  exact IsLocalizedModule.of_restrictScalars (Submonoid.powers s)
    (IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s)

/-- Full normal-order base change, with O acting by precomposition.
The base localization is the actual old N→O normal-order inclusion. -/
lemma baseChange [Module.FinitePresentation P N] :
    IsBaseChange O (IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s) := by
  letI := IntegralClosurePrincipalLocalization318.localization (Q:=Q) (B:=B) s
  letI := localization (Q:=Q) (B:=B) s
  exact IsLocalizedModule.isBaseChange (Submonoid.powers (algebraMap P N s)) O
    (IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s)

@[expose] def equivalence [Module.FinitePresentation P N] :
    O ⊗[N] (N →ₗ[P] P) ≃ₗ[O] (O →ₗ[P] Q) :=
  (baseChange (Q:=Q) (B:=B) s).equiv

lemma one_value [Module.FinitePresentation P N] (f : N →ₗ[P] P) (n : N) :
    equivalence (Q:=Q) (B:=B) s (1 ⊗ₜ[N] f) (i n)=algebraMap P Q (f n) := by
  rw [equivalence,IsBaseChange.equiv_tmul,one_smul,
    IntegralClosureDualOrderLinearity318.map_value]

lemma integral_tensor_value [Module.FinitePresentation P N]
    (a n : N) (f : N →ₗ[P] P) :
    equivalence (Q:=Q) (B:=B) s (i a ⊗ₜ[N] f) (i n)=
      algebraMap P Q (f (a*n)) := by
  rw [equivalence,IsBaseChange.equiv_tmul]
  change IntegralClosureDualOrderLinearity318.map (Q:=Q) (B:=B) s f (i a*i n)=_
  rw [←map_mul,IntegralClosureDualOrderLinearity318.map_value]
end IntegralClosureDualOrderBaseChange318
