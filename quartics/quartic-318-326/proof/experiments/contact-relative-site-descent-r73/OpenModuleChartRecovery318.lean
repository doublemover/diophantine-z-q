module
public import OpenModuleTransition318
public section
noncomputable section
namespace OpenModuleChartRecovery318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : Data U M)

/-- On a subopen of a chart, read its original local component. -/
@[expose] def evaluate (i : ι) (W : X.Opens) (hi : W ≤ U i) (s : (OpenModuleTransition318.sections D) W) : Γ(M i,W) :=
  res (M i) (le_inf le_rfl hi) (s.val i)

lemma evaluate_restrict (i : ι) {W V : X.Opens} (h : V ≤ W) (hi : V ≤ U i)
    (s : (OpenModuleTransition318.sections D) W) : evaluate D i V hi ((OpenModuleTransition318.restrict D) h s) =
      res (M i) (le_inf h hi) (s.val i) := by
  exact res_res (M i) _ _ _

/-- The original transition isomorphisms extend a section in a chosen
chart to an actual matching family on that same subopen. -/
@[expose] def fromChart (i : ι) (W : X.Opens) (hi : W ≤ U i) (s : Γ(M i,W)) : (OpenModuleTransition318.sections D) W :=
  makeSection D W (fun j => D.transition i j (W ⊓ U j) (inf_le_left.trans hi) inf_le_right
      (res (M i) inf_le_left s)) (by
    intro j k V hW hj hk
    rw [D.natural, D.natural, res_res, res_res, D.cocycle])

lemma evaluate_fromChart (i : ι) (W : X.Opens) (hi : W ≤ U i) (s : Γ(M i,W)) :
    evaluate D i W hi (fromChart D i W hi s) = s := by
  change res (M i) (le_inf le_rfl hi)
    (D.transition i i (W ⊓ U i) (inf_le_left.trans hi) inf_le_right
      (res (M i) inf_le_left s)) = s
  rw [D.identity, res_res, res_self]

lemma fromChart_evaluate (i : ι) (W : X.Opens) (hi : W ≤ U i) (s : (OpenModuleTransition318.sections D) W) :
    fromChart D i W hi (evaluate D i W hi s) = s := by
  apply Subtype.ext
  funext j
  change D.transition i j (W ⊓ U j) (inf_le_left.trans hi) inf_le_right
    (res (M i) inf_le_left (res (M i) (le_inf le_rfl hi) (s.val i))) = s.val j
  rw [res_res]
  have h := compatible D W s i j (W ⊓ U j) inf_le_left (inf_le_left.trans hi) inf_le_right
  simpa only [res_self] using h

/-- Genuine chart recovery of every matching-family module. This is not
an assumed local trivialization of a future global object. -/
@[expose] def chartEquiv (i : ι) (W : X.Opens) (hi : W ≤ U i) :
    (OpenModuleTransition318.sections D) W ≃ Γ(M i,W) where
  toFun := evaluate D i W hi
  invFun := fromChart D i W hi
  left_inv := fromChart_evaluate D i W hi
  right_inv := evaluate_fromChart D i W hi

lemma evaluate_natural (i : ι) {W V : X.Opens} (hi : W ≤ U i) (h : V ≤ W)
    (s : (OpenModuleTransition318.sections D) W) : res (M i) h (evaluate D i W hi s) =
      evaluate D i V (h.trans hi) ((OpenModuleTransition318.restrict D) h s) := by
  rw [evaluate_restrict]
  exact res_res (M i) _ _ _

/-- The recovered chart comparisons have exactly the original transition
on every common subopen, before any object gluing is invoked. -/
lemma evaluate_transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (s : (OpenModuleTransition318.sections D) W) : D.transition i j W hi hj (evaluate D i W hi s) =
      evaluate D j W hj s := compatible D W s i j W le_rfl hi hj
end OpenModuleChartRecovery318
