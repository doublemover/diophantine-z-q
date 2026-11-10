module
public import StructureAdditiveSheaf318
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Tactic.Abel

public section
noncomputable section
namespace AdditiveSheafSections318
open CategoryTheory TopologicalSpace Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}
abbrev ASheaf := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
variable (F : ASheaf (X:=X))
abbrev Sec (U : Opens X) := F.obj.obj (op U)
@[expose] def res {U V : Opens X} (h : V ≤ U) : Sec F U →+ Sec F V :=
  (F.obj.map (homOfLE h).op).hom
@[simp] theorem res_res {U V W : Opens X} (h : V ≤ U) (k : W ≤ V) (s : Sec F U) :
    res F k (res F h s) = res F (k.trans h) s := by
  change F.obj.map _ (F.obj.map _ s) = _
  rw [← F.obj.map_comp_apply]
  rfl
variable {F} {G : ASheaf (X:=X)}
theorem hom_res (a : F ⟶ G) {U V : Opens X} (h : V ≤ U) (s : Sec F U) :
    res G h (a.hom.app _ s) = a.hom.app _ (res F h s) := by
  exact (ConcreteCategory.congr_hom (a.hom.naturality (homOfLE h).op) s).symm

theorem app_injective (a : F ⟶ G) [Mono a] (U : Opens X) :
    Function.Injective (a.hom.app (op U)) := by
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

end AdditiveSheafSections318
