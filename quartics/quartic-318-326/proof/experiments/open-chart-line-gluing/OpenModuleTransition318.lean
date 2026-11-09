module
public import ModuleLocalGluing318
public section
noncomputable section
namespace OpenModuleTransition318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ModuleLocalGluing318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (M : ι → X.Modules)

/-- Actual transition maps on every subopen of each pair of charts.
The ambient sheaves can be direct images of sheaves on the charts; their
values away from their own chart are never used by the gluing construction. -/
structure Data where
  transition : ∀ i j (V : X.Opens), V ≤ U i → V ≤ U j →
    Γ(M i,V) ≃ₗ[Γ(X,V)] Γ(M j,V)
  natural : ∀ i j (V W : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (h : W ≤ V) (s : Γ(M i,V)),
    res (M j) h (transition i j V hi hj s) =
      transition i j W (h.trans hi) (h.trans hj) (res (M i) h s)
  identity : ∀ i (V : X.Opens) (hi : V ≤ U i) (s : Γ(M i,V)),
    transition i i V hi hi s = s
  cocycle : ∀ i j k (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (hk : V ≤ U k) (s : Γ(M i,V)),
    transition j k V hj hk (transition i j V hi hj s) = transition i k V hi hk s

variable {U M} (D : Data U M)

/-- Families are compared on every actual common subopen, so restriction
does not require silently replacing an overlap by a different presentation. -/
def Compatible (W : X.Opens) (s : ∀ i, Γ(M i,W ⊓ U i)) : Prop :=
  ∀ i j (V : X.Opens) (hW : V ≤ W) (hi : V ≤ U i) (hj : V ≤ U j),
    D.transition i j V hi hj (res (M i) (le_inf hW hi) (s i)) =
      res (M j) (le_inf hW hj) (s j)

/-- The component module retains restriction of the original scalar ring
Γ(X,W) to the exact original local open W intersect U i. -/
abbrev component (W : X.Opens) (i : ι) : ModuleCat Γ(X,W) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op).hom).obj
    ((M i).val.obj (op (W ⊓ U i)))

/-- The actual matching-family module over each original ambient open. -/
@[expose] def sections (W : X.Opens) : Submodule Γ(X,W) (∀ i, component (U := U) (M := M) W i) where
  carrier := {s | D.Compatible W s}
  zero_mem' := by
    intro i j V hW hi hj
    simp only [res, map_zero, Pi.zero_apply]
  add_mem' := by
    intro s t hs ht i j V hW hi hj
    simp only [Pi.add_apply, res, map_add]
    exact congrArg₂ (· + ·) (hs i j V hW hi hj) (ht i j V hW hi hj)
  smul_mem' := by
    intro a s hs i j V hW hi hj
    change D.transition i j V hi hj
      (res (M i) (le_inf hW hi)
        ((X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op a) • s i)) =
      res (M j) (le_inf hW hj)
        ((X.presheaf.map (homOfLE (show W ⊓ U j ≤ W from inf_le_left)).op a) • s j)
    simp only [res, Scheme.Modules.map_smul, map_smul]
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp,
      ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    exact congrArg (fun x => (X.presheaf.map (homOfLE hW).op a) • x)
      (hs i j V hW hi hj)

/-- Restrict the original matching family componentwise. -/
@[expose] def restrict {W V : X.Opens} (h : V ≤ W) (s : D.sections W) : D.sections V :=
  ⟨fun i => res (M i) (inf_le_inf_right (U i) h) (s.val i), by
    intro i j Z hZ hi hj
    simpa only [res_res] using s.property i j Z (hZ.trans h) hi hj⟩

lemma restrict_apply {W V : X.Opens} (h : V ≤ W) (s : D.sections W) (i : ι) :
    (D.restrict h s).val i = res (M i) (inf_le_inf_right (U i) h) (s.val i) := rfl

lemma restrict_self (W : X.Opens) (s : D.sections W) : D.restrict le_rfl s = s := by
  apply Subtype.ext
  funext i
  exact res_self (M i) (W ⊓ U i) (s.val i)

lemma restrict_restrict {W V Z : X.Opens} (h : V ≤ W) (k : Z ≤ V) (s : D.sections W) :
    D.restrict k (D.restrict h s) = D.restrict (k.trans h) s := by
  apply Subtype.ext
  funext i
  exact res_res (M i) _ _ _
end OpenModuleTransition318
