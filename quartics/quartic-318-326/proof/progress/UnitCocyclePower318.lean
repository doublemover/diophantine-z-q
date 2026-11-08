module
public import UnitCocycleProductLaws318
public section
noncomputable section
namespace UnitCocyclePower318
open CategoryTheory TopologicalSpace UnitTransitionCocycle318
universe u v
variable {X:TopCat.{u}} {F:X.Presheaf CommGrpCat.{u}} {ι:Type v} {U:ι→Opens X}
/-- Actual powers of the original transition units on unchanged intersections. -/
@[expose] def power (c:Cocycle F U) (n:ℕ):Cocycle F U where
  transition i j:=c.transition i j^n
  diagonal i:=by rw [c.diagonal,one_pow]
  triple i j k:=by
    simp only [map_pow]
    rw [←mul_pow,c.triple]
lemma transition (c:Cocycle F U) (n:ℕ) (i j:ι):
    (power c n).transition i j=c.transition i j^n:=rfl
lemma zero (c:Cocycle F U):power c 0=UnitCocycleOne318.one F U:=by
  apply Cocycle.ext
  intro i j
  exact pow_zero _
lemma succ (c:Cocycle F U) (n:ℕ):
    power c (n+1)=UnitCocycleProduct318.product (power c n) c:=by
  apply Cocycle.ext
  intro i j
  exact pow_succ _ _
lemma map_power {G:X.Presheaf CommGrpCat.{u}} (a:F⟶G) (c:Cocycle F U) (n:ℕ):
    map a (power c n)=power (map a c) n:=by
  apply Cocycle.ext
  intro i j
  exact (a.app _).hom.map_pow _ _
end UnitCocyclePower318
