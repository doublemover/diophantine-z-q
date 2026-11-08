module
public import UnitTransitionCocycle318
public section
noncomputable section
namespace UnitCocycleProduct318
open CategoryTheory Opposite TopologicalSpace UnitTransitionCocycle318
universe u v
variable {X:TopCat.{u}} {F G:X.Presheaf CommGrpCat.{u}} {ι:Type v} {U:ι→Opens X}
/-- Pointwise product on the unchanged original complete intersections. -/
@[expose] def product (c d:Cocycle F U):Cocycle F U where
  transition i j:=c.transition i j*d.transition i j
  diagonal i:=by rw [c.diagonal,d.diagonal,one_mul]
  triple i j k:=by
    simp only [map_mul]
    rw [mul_mul_mul_comm,c.triple,d.triple]
lemma map_product (a:F⟶G) (c d:Cocycle F U):
    map a (product c d)=product (map a c) (map a d):=by
  apply Cocycle.ext
  intro i j
  exact (a.app _).hom.map_mul _ _
end UnitCocycleProduct318
