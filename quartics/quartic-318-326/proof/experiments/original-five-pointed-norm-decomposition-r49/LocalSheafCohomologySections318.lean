module
public import SheafInverseImageConstants318

public section
noncomputable section
namespace LocalSheafCohomologySections318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}
abbrev ASheaf := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
abbrev freePresheaf (U : Opens X) := yoneda.obj U ⋙ AddCommGrpCat.free
abbrev generator (U : Opens X) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (freePresheaf U)

@[expose] def sectionLift (F : ASheaf (X:=X)) (U : Opens X) (s : F.obj.obj (op U)) :
    freePresheaf U ⟶ F.obj where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift
    (fun g : V.unop ⟶ U => F.obj.map g.op s))
  naturality V W i := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (fun g : W.unop ⟶ U => F.obj.map g.op s)
      (FreeAbelianGroup.map (fun g : V.unop ⟶ U => i.unop ≫ g) (FreeAbelianGroup.of g)) =
      F.obj.map i (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op s) (FreeAbelianGroup.of g))
    simp only [FreeAbelianGroup.map_of_apply,FreeAbelianGroup.lift_apply_of]
    rw [← F.obj.map_comp_apply]
    rfl

@[expose] def presheafEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    (freePresheaf U ⟶ F.obj) ≃ F.obj.obj (op U) where
  toFun f := f.app (op U) (FreeAbelianGroup.of (𝟙 U))
  invFun s := sectionLift F U s
  left_inv f := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    have h := ConcreteCategory.congr_hom (f.naturality g.op) (FreeAbelianGroup.of (𝟙 U))
    simpa [sectionLift,freePresheaf] using h.symm
  right_inv s := by
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of (𝟙 U)) = s
    rw [FreeAbelianGroup.lift_apply_of]
    change F.obj.map (𝟙 (op U)) s = s
    rw [F.obj.map_id]
    rfl

/-- The genuine free-abelian sheaf generator of a local cohomology group represents original sections. -/
@[expose] def sectionEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    (generator U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homEquiv
    (freePresheaf U) F).trans (presheafEquiv F U)

theorem sectionEquiv_naturality {F G : ASheaf (X:=X)} (a : F ⟶ G)
    (U : Opens X) (f : generator U ⟶ F) :
    sectionEquiv G U (f ≫ a) = a.hom.app (op U) (sectionEquiv F U f) := by
  exact congrArg (presheafEquiv G U)
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homEquiv_naturality_right f a)

/-- Actual local Ext-defined degree-zero cohomology equals original sections. -/
@[expose] def zeroEquiv (F : ASheaf (X:=X)) (U : Opens X) :
    (F.H' 0 U) ≃ F.obj.obj (op U) :=
  Ext.homEquiv₀.trans (sectionEquiv F U)

theorem zeroEquiv_naturality {F G : ASheaf (X:=X)} (a : F ⟶ G)
    (U : Opens X) (x : F.H' 0 U) :
    zeroEquiv G U (x.comp (Ext.mk₀ a) (add_zero 0)) =
      a.hom.app (op U) (zeroEquiv F U x) := by
  have h : Ext.homEquiv₀ (x.comp (Ext.mk₀ a) (add_zero 0)) = Ext.homEquiv₀ x ≫ a := by
    apply (Ext.mk₀_bijective _ _).injective
    simp only [Ext.mk₀_homEquiv₀_apply,← Ext.mk₀_comp_mk₀]
  exact (congrArg (sectionEquiv G U) h).trans (sectionEquiv_naturality a U (Ext.homEquiv₀ x))

end LocalSheafCohomologySections318
