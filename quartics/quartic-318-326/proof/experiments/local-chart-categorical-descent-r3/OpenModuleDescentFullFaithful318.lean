module
public import OpenModuleDescentMaps318
public section
noncomputable section
namespace OpenModuleDescentFullFaithful318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318 OpenModuleChartRecovery318 OpenModuleGluedSheaf318 OpenModuleDescentMaps318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
  {M N : ι → X.Modules} {D : Data U M} {E : Data U N}

lemma fromChart_natural (D : Data U M) (i : ι) {W V : X.Opens}
    (hi : W ≤ U i) (h : V ≤ W) (s : Γ(M i,W)) :
    restrict D h (fromChart D i W hi s) = fromChart D i V (h.trans hi) (res (M i) h s) := by
  apply (chartEquiv D i V (h.trans hi)).injective
  change evaluate D i V (h.trans hi) _ = evaluate D i V (h.trans hi) _
  rw [← evaluate_natural, evaluate_fromChart, evaluate_fromChart]

lemma fromChart_transition (D : Data U M) (i j : ι) (W : X.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) (s : Γ(M i,W)) :
    fromChart D j W hj (D.transition i j W hi hj s) = fromChart D i W hi s := by
  apply (chartEquiv D j W hj).injective
  change evaluate D j W hj _ = evaluate D j W hj _
  rw [evaluate_fromChart, ← evaluate_transition D i j W hi hj, evaluate_fromChart]

lemma component_from_evaluate (D : Data U M) (W : X.Opens) (i : ι) (s : sections D W) :
    evaluate D i (W ⊓ U i) inf_le_right (restrict D inf_le_left s) = s.val i := by
  rw [evaluate_restrict]
  exact res_self (M i) (W ⊓ U i) (s.val i)

/-- Equality of maps is detected by their displayed chart comparison
squares. No unrelated global extension of any input chart map is assumed. -/
lemma sheafMap_ext {f g : sheaf D ⟶ sheaf E}
    (h : ∀ i (W : X.Opens) (hi : W ≤ U i) (s : sections D W),
      evaluate E i W hi (f.val.app (op W) s) = evaluate E i W hi (g.val.app (op W) s)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  apply Subtype.ext
  funext i
  have he := h i (W.unop ⊓ U i) inf_le_right (restrict D inf_le_left s)
  have hf := PresheafOfModules.naturality_apply f.val
    (homOfLE (show W.unop ⊓ U i ≤ W.unop from inf_le_left)).op s
  have hg := PresheafOfModules.naturality_apply g.val
    (homOfLE (show W.unop ⊓ U i ≤ W.unop from inf_le_left)).op s
  change f.val.app (op (W.unop ⊓ U i)) (restrict D inf_le_left s) =
    restrict E inf_le_left (f.val.app W s) at hf
  change g.val.app (op (W.unop ⊓ U i)) (restrict D inf_le_left s) =
    restrict E inf_le_left (g.val.app W s) at hg
  rw [hf, hg, component_from_evaluate, component_from_evaluate] at he
  exact he

/-- Every global map induces the original local chart maps, through the
same displayed comparison isomorphisms used in object reconstruction. -/
@[expose] def localize (f : sheaf D ⟶ sheaf E) : Map D E where
  app i W hi := (chartLinearEquiv E i W hi).toLinearMap.comp
    ((f.val.app (op W)).hom.comp (chartLinearEquiv D i W hi).symm.toLinearMap)
  natural i W V hi h s := by
    change res (N i) h (evaluate E i W hi (f.val.app (op W) (fromChart D i W hi s))) =
      evaluate E i V (h.trans hi) (f.val.app (op V) (fromChart D i V (h.trans hi) (res (M i) h s)))
    rw [evaluate_natural]
    have hf := PresheafOfModules.naturality_apply f.val (homOfLE h).op (fromChart D i W hi s)
    change f.val.app (op V) (restrict D h (fromChart D i W hi s)) =
      restrict E h (f.val.app (op W) (fromChart D i W hi s)) at hf
    rw [← hf, fromChart_natural]
  compatible i j W hi hj s := by
    change E.transition i j W hi hj (evaluate E i W hi (f.val.app (op W) (fromChart D i W hi s))) =
      evaluate E j W hj (f.val.app (op W) (fromChart D j W hj (D.transition i j W hi hj s)))
    rw [evaluate_transition, fromChart_transition]

lemma localize_apply (f : sheaf D ⟶ sheaf E) (i : ι) (W : X.Opens)
    (hi : W ≤ U i) (s : Γ(M i,W)) :
    (localize f).app i W hi s = evaluate E i W hi (f.val.app (op W) (fromChart D i W hi s)) := rfl

lemma localize_sheafMap (f : Map D E) : localize (sheafMap f) = f := by
  apply Map.ext
  intro i W hi s
  rw [localize_apply, evaluate_sheafMap, evaluate_fromChart]

lemma sheafMap_localize (f : sheaf D ⟶ sheaf E) : sheafMap (localize f) = f := by
  apply sheafMap_ext
  intro i W hi s
  rw [evaluate_sheafMap, localize_apply, fromChart_evaluate]

/-- Morphism effectivity is a genuine bijection with all morphisms of the
actual reconstructed module sheaves, not merely with chosen representatives. -/
@[expose] def homEquiv : Map D E ≃ (sheaf D ⟶ sheaf E) where
  toFun := sheafMap
  invFun := localize
  left_inv := localize_sheafMap
  right_inv := sheafMap_localize

lemma sheafMap_unique (f : Map D E) (g : sheaf D ⟶ sheaf E)
    (h : ∀ i (W : X.Opens) (hi : W ≤ U i) (s : sections D W),
      evaluate E i W hi (g.val.app (op W) s) = f.app i W hi (evaluate D i W hi s)) :
    g = sheafMap f := by
  apply sheafMap_ext
  intro i W hi s
  rw [h, evaluate_sheafMap]

/-- Original mutually inverse compatible local maps yield a genuine
isomorphism of the reconstructed sheaves, with those exact hom and inv maps. -/
@[expose] def gluedIso (f : Map D E) (g : Map E D)
    (hfg : compose f g = identity D) (hgf : compose g f = identity E) : sheaf D ≅ sheaf E where
  hom := sheafMap f
  inv := sheafMap g
  hom_inv_id := by rw [← sheafMap_compose, hfg, sheafMap_identity]
  inv_hom_id := by rw [← sheafMap_compose, hgf, sheafMap_identity]
end OpenModuleDescentFullFaithful318
