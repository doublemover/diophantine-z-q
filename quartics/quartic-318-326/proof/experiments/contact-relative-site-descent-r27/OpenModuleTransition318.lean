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

/-- The original module restriction is semilinear for the original
structure-sheaf restriction. Keep this typed identity opaque downstream. -/
lemma res_smul (A : X.Modules) {W V : X.Opens} (h : V ≤ W)
    (a : Γ(X,W)) (s : Γ(A,W)) :
    res A h (a • s) = (X.presheaf.map (homOfLE h).op a) • res A h s :=
  A.val.map_smul (homOfLE h).op a s

/-- Compose exactly the original scalar restriction maps. -/
lemma scalar_res_res {W V Z : X.Opens} (h : V ≤ W) (k : Z ≤ V) (a : Γ(X,W)) :
    X.presheaf.map (homOfLE k).op (X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (k.trans h)).op a :=
  (CategoryTheory.Functor.map_comp_apply X.presheaf (homOfLE h).op (homOfLE k).op a).symm

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
@[expose] def Compatible (W : X.Opens) (s : ∀ i, Γ(M i,W ⊓ U i)) : Prop :=
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
  carrier := {s | (OpenModuleTransition318.Compatible D) W s}
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
    rw [res_smul, res_smul, map_smul, scalar_res_res, scalar_res_res]
    exact congrArg (fun x => (X.presheaf.map (homOfLE hW).op a) • x)
      (hs i j V hW hi hj)

/-- Public constructor for the actual original matching-family submodule,
with its compatibility equation exposed rather than opaque membership. -/
@[expose] def makeSection (W : X.Opens) (s : ∀ i, Γ(M i,W ⊓ U i))
    (hs : ∀ i j (V : X.Opens) (hW : V ≤ W) (hi : V ≤ U i) (hj : V ≤ U j),
      D.transition i j V hi hj (res (M i) (le_inf hW hi) (s i)) =
        res (M j) (le_inf hW hj) (s j)) : sections D W := ⟨s, hs⟩

/-- Public accessor states the genuine original common-subopen equation. -/
lemma compatible (W : X.Opens) (s : sections D W) (i j : ι) (V : X.Opens)
    (hW : V ≤ W) (hi : V ≤ U i) (hj : V ≤ U j) :
    D.transition i j V hi hj (res (M i) (le_inf hW hi) (s.val i)) =
      res (M j) (le_inf hW hj) (s.val j) := s.property i j V hW hi hj

/-- Restrict the original matching family componentwise. -/
@[expose] def restrict {W V : X.Opens} (h : V ≤ W) (s : (OpenModuleTransition318.sections D) W) : (OpenModuleTransition318.sections D) V :=
  ⟨fun i => res (M i) (inf_le_inf_right (U i) h) (s.val i), by
    intro i j Z hZ hi hj
    simpa only [res_res] using s.property i j Z (hZ.trans h) hi hj⟩

lemma restrict_apply {W V : X.Opens} (h : V ≤ W) (s : (OpenModuleTransition318.sections D) W) (i : ι) :
    ((OpenModuleTransition318.restrict D) h s).val i = res (M i) (inf_le_inf_right (U i) h) (s.val i) := rfl

lemma restrict_self (W : X.Opens) (s : (OpenModuleTransition318.sections D) W) : (OpenModuleTransition318.restrict D) le_rfl s = s := by
  apply Subtype.ext
  funext i
  exact res_self (M i) (W ⊓ U i) (s.val i)

lemma restrict_restrict {W V Z : X.Opens} (h : V ≤ W) (k : Z ≤ V) (s : (OpenModuleTransition318.sections D) W) :
    (OpenModuleTransition318.restrict D) k ((OpenModuleTransition318.restrict D) h s) = (OpenModuleTransition318.restrict D) (k.trans h) s := by
  apply Subtype.ext
  funext i
  exact res_res (M i) _ _ _
end OpenModuleTransition318
