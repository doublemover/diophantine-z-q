module
public import GlobalComparisonRestriction318
public section
noncomputable section
namespace ModuleRestrictionCoverFaithful318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ModuleLocalGluing318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

lemma over_eq_of_restrict_eq (U : X.Opens) {a b : M ⟶ N}
    (h : (Scheme.Modules.restrictFunctor U.ι).map a = (Scheme.Modules.restrictFunctor U.ι).map b) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map a =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map b := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  apply (cancel_mono (Scheme.Modules.overFunctorEquiv U).hom.app N).mp
  have ha := (Scheme.Modules.overFunctorEquiv U).hom.naturality a
  have hb := (Scheme.Modules.overFunctorEquiv U).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [ha,hb,h]

/-- Original sheaf maps are detected on an arbitrary full open cover,
without any finiteness or affineness assumption on its intersections. -/
lemma hom_ext {ι : Type u} (U : ι → X.Opens) (hc : (⊤ : X.Opens) ≤ iSup U)
    {a b : M ⟶ N} (h : ∀ i,
      (Scheme.Modules.restrictFunctor (U i).ι).map a =
        (Scheme.Modules.restrictFunctor (U i).ι).map b) : a = b := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply ext_value hc W
  intro i
  have hi := over_eq_of_restrict_eq (U i) (h i)
  have hv := congrArg (fun q => q.val.app
    (op (Over.mk (homOfLE (show W ⊓ U i ≤ U i from inf_le_right))))
      (res M (show W ⊓ U i ≤ W from inf_le_left) s)) hi
  have ha := (congrArg (fun q => q s) (a.mapPresheaf.naturality (homOfLE
    (show W ⊓ U i ≤ W from inf_le_left)).op)).symm
  have hb := (congrArg (fun q => q s) (b.mapPresheaf.naturality (homOfLE
    (show W ⊓ U i ≤ W from inf_le_left)).op)).symm
  change res N inf_le_left (a.app W s) = res N inf_le_left (b.app W s)
  rw [ha,hb]
  exact hv
end ModuleRestrictionCoverFaithful318
