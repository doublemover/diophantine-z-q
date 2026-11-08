module
public import UnitCocycleProduct318
public import UnitCocycleOne318
public section
noncomputable section
namespace UnitCocycleProductLaws318
open CategoryTheory TopologicalSpace UnitTransitionCocycle318 UnitCocycleProduct318
universe u v
variable {X:TopCat.{u}} {F:X.Presheaf CommGrpCat.{u}} {ι:Type v} {U:ι→Opens X}
lemma assoc (c d e:Cocycle F U):product (product c d) e=product c (product d e):=by
  apply Cocycle.ext
  intro i j
  exact mul_assoc _ _ _
lemma comm (c d:Cocycle F U):product c d=product d c:=by
  apply Cocycle.ext
  intro i j
  exact mul_comm _ _
lemma one_product (c:Cocycle F U):product (UnitCocycleOne318.one F U) c=c:=by
  apply Cocycle.ext
  intro i j
  exact one_mul _
lemma product_one (c:Cocycle F U):product c (UnitCocycleOne318.one F U)=c:=by
  apply Cocycle.ext
  intro i j
  exact mul_one _
end UnitCocycleProductLaws318
