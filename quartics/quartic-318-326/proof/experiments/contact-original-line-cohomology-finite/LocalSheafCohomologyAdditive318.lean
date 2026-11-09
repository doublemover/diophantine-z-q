module
public import LocalSheafCohomologySections318
public section
noncomputable section
namespace LocalSheafCohomologyAdditive318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}
@[expose] def presheafAddEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    (freePresheaf U ⟶ F.obj) ≃+ F.obj.obj (op U) :=
  { presheafEquiv F U with map_add' := fun _f _g => rfl }
@[expose] def sectionAddEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    (generator U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homAddEquiv
    (freePresheaf U) F).trans (presheafAddEquiv F U)
@[expose] def zeroAddEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    F.H' 0 U ≃+ F.obj.obj (op U) := Ext.addEquiv₀.trans (sectionAddEquiv F U)
end LocalSheafCohomologyAdditive318
