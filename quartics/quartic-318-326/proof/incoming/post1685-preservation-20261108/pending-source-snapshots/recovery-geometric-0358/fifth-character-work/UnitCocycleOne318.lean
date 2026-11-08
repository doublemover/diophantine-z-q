module
public import UnitTransitionCocycle318
public section
noncomputable section
namespace UnitCocycleOne318
open CategoryTheory Opposite TopologicalSpace
universe u v
variable {X:TopCat.{u}} {ι:Type v}
@[expose] def one (F:X.Presheaf CommGrpCat.{u}) (U:ι→Opens X):
    UnitTransitionCocycle318.Cocycle F U where
  transition _ _:=1
  diagonal _:=rfl
  triple _ _ _:=by simp [UnitTransitionCocycle318.restrict]
lemma map_one {F G:X.Presheaf CommGrpCat.{u}} (a:F⟶G) (U:ι→Opens X):
    UnitTransitionCocycle318.map a (one F U)=one G U:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact map_one (a.app _).hom
end UnitCocycleOne318
