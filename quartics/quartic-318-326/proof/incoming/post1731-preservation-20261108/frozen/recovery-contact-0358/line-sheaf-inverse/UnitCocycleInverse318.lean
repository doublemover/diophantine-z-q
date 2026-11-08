module
public import UnitCocycleProduct318
public import UnitCocycleOne318
public section
noncomputable section
namespace UnitCocycleInverse318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
universe u v
variable {X:TopCat.{u}} {F G:X.Presheaf CommGrpCat.{u}} {ι:Type v} {U:ι→Opens X}
/-- Inverse transition units on exactly the same complete intersections. -/
@[expose] def inverse (c:Cocycle F U):Cocycle F U where
  transition i j:=(c.transition i j)⁻¹
  diagonal i:=by rw [c.diagonal,inv_one]
  triple i j k:=by
    simp only [map_inv]
    rw [←mul_inv,c.triple]
lemma transition (c:Cocycle F U) (i j:ι):
    (inverse c).transition i j=(c.transition i j)⁻¹:=rfl
lemma product_inverse (c:Cocycle F U):
    UnitCocycleProduct318.product c (inverse c)=UnitCocycleOne318.one F U:=by
  apply Cocycle.ext
  intro i j
  exact mul_inv_cancel _
lemma inverse_product (c:Cocycle F U):
    UnitCocycleProduct318.product (inverse c) c=UnitCocycleOne318.one F U:=by
  apply Cocycle.ext
  intro i j
  exact inv_mul_cancel _
lemma inverse_inverse (c:Cocycle F U):inverse (inverse c)=c:=by
  apply Cocycle.ext
  intro i j
  exact inv_inv _
lemma map_inverse (a:F⟶G) (c:Cocycle F U):
    map a (inverse c)=inverse (map a c):=by
  apply Cocycle.ext
  intro i j
  exact (a.app _).hom.map_inv _
end UnitCocycleInverse318
