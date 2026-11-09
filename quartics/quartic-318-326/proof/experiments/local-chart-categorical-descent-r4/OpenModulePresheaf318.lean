module
public import OpenModuleChartRecovery318
public section
noncomputable section
namespace OpenModulePresheaf318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : Data U M)

lemma restrict_add {W V : X.Opens} (h : V ≤ W) (s t : (OpenModuleTransition318.sections D) W) :
    (OpenModuleTransition318.restrict D) h (s + t) = (OpenModuleTransition318.restrict D) h s + (OpenModuleTransition318.restrict D) h t := by
  apply Subtype.ext
  funext i
  exact map_add _ _ _

lemma restrict_smul {W V : X.Opens} (h : V ≤ W) (a : Γ(X,W)) (s : (OpenModuleTransition318.sections D) W) :
    (OpenModuleTransition318.restrict D) h (a • s) = (X.presheaf.map (homOfLE h).op a) • (OpenModuleTransition318.restrict D) h s := by
  apply Subtype.ext
  funext i
  change res (M i) (inf_le_inf_right (U i) h)
      ((X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op a) • s.val i) =
    (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op
      (X.presheaf.map (homOfLE h).op a)) • res (M i) (inf_le_inf_right (U i) h) (s.val i)
  rw [res_smul, scalar_res_res, scalar_res_res]
  rfl

/-- The actual additive presheaf of matching local section families. -/
@[expose] def presheaf : TopCat.Presheaf AddCommGrpCat X where
  obj W := AddCommGrpCat.of ((OpenModuleTransition318.sections D) W.unop)
  map h := AddCommGrpCat.ofHom
    { toFun := (OpenModuleTransition318.restrict D) (leOfHom h.unop)
      map_zero' := by
        apply Subtype.ext
        funext i
        exact map_zero _
      map_add' := restrict_add D (leOfHom h.unop) }
  map_id W := by
    ext s
    exact (OpenModuleTransition318.restrict_self D) W.unop s
  map_comp f g := by
    ext s
    exact ((OpenModuleTransition318.restrict_restrict D) (leOfHom f.unop) (leOfHom g.unop) s).symm

/-- Expose the unchanged section-ring action to the presheaf constructor. -/
instance sectionModule (W : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((presheaf D).obj W) :=
  inferInstanceAs (Module Γ(X,W.unop) ((OpenModuleTransition318.sections D) W.unop))

/-- Its scalar action is over the original structure sheaf on each open. -/
@[expose] def modulePresheaf : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (presheaf D) (fun {_ _} f a s =>
    restrict_smul D (leOfHom f.unop) a s)

lemma presheaf_restrict {W V : X.Opens} (h : V ≤ W) (s : (OpenModuleTransition318.sections D) W) :
    (presheaf D).map (homOfLE h).op s = (OpenModuleTransition318.restrict D) h s := rfl
end OpenModulePresheaf318
