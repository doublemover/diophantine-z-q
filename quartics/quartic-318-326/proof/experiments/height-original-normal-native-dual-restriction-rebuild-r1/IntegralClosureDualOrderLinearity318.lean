module
public import ValuedDualPrecomposition318
public import IntegralClosureDualRestrictionSeparation318
public section
noncomputable section
namespace IntegralClosureDualOrderLinearity318
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

@[instance_reducible] def sourceTower : IsScalarTower P N (N →ₗ[P] P) :=
  ValuedDualPrecomposition318.baseTower P N P

@[instance_reducible] def targetBaseTower : IsScalarTower P N (O →ₗ[P] Q) where
  smul_assoc p n f := by
    apply LinearMap.ext; intro x
    change f (i (p • n)*x)=p • f (i n*x)
    rw [map_smul,smul_mul_assoc,map_smul]

@[instance_reducible] def targetOrderTower : IsScalarTower N O (O →ₗ[P] Q) where
  smul_assoc n o f := by
    apply LinearMap.ext; intro x
    change f ((i n*o)*x)=f (o*(i n*x))
    congr 1; ring

/-- The ACTUAL old Hom extension is N-linear for multiplication on inputs.
Equality is proved on every old integral input using full localization separation. -/
lemma map_action (n : N) (f : N →ₗ[P] P) :
    IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s (n • f)=
      n • IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s f := by
  apply IntegralClosureDualRestrictionSeparation318.ext s
  intro m
  change IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s
      (ValuedDualPrecomposition318.action P N P n f) (i m)=
    IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s f (i n*i m)
  rw [IntegralClosureFullDualLocalization318.map_value,
    ←map_mul,IntegralClosureFullDualLocalization318.map_value] <;> rfl

@[expose] def map : (N →ₗ[P] P) →ₗ[N] (O →ₗ[P] Q) where
  toFun := IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s
  map_add' := (IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s).map_add
  map_smul' := map_action s

local instance : IsScalarTower P N (N →ₗ[P] P) := sourceTower
local instance : IsScalarTower P N (O →ₗ[P] Q) := targetBaseTower

/-- Literal equality with the old map, not identification merely by its type. -/
lemma restrictScalars :
    (map (Q:=Q) (B:=B) s).restrictScalars P=
      IntegralClosureFullDualLocalization318.map (Q:=Q) (B:=B) s := by
  apply LinearMap.ext
  intro f
  rfl

lemma map_value (f : N →ₗ[P] P) (n : N) :
    map (Q:=Q) (B:=B) s f (i n)=algebraMap P Q (f n) :=
  IntegralClosureFullDualLocalization318.map_value s f n
end IntegralClosureDualOrderLinearity318
