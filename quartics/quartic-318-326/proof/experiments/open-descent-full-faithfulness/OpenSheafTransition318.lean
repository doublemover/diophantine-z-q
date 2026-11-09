module
public import OpenModuleGluedSheaf318
public section
noncomputable section
namespace OpenSheafTransition318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B : X.Modules}

/-- Restriction of an actual over-open sheaf isomorphism, normalized back
to the unchanged original ambient sheaves by the canonical over comparisons. -/
@[expose] def restrictIso {U V : X.Opens} (e : A.over U ≅ B.over U) (h : V ≤ U) :
    A.over V ≅ B.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app A).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso e ≪≫
      (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app B

/-- Exact original section component of an over-open sheaf isomorphism. -/
@[expose] def component {U : X.Opens} (e : A.over U ≅ B.over U)
    (V : X.Opens) (h : V ≤ U) : Γ(A,V) ≃ₗ[Γ(X,V)] Γ(B,V) :=
  (((SheafOfModules.forget (X.ringCatSheaf.over U)) ⋙
    PresheafOfModules.evaluation _ (op (Over.mk (homOfLE h)))).mapIso e).toLinearEquiv

lemma component_natural {U : X.Opens} (e : A.over U ≅ B.over U)
    (V W : X.Opens) (hV : V ≤ U) (h : W ≤ V) (s : Γ(A,V)) :
    ModuleLocalGluing318.res B h (component e V hV s) =
      component e W (h.trans hV) (ModuleLocalGluing318.res A h s) := by
  let f : Over.mk (homOfLE (h.trans hV)) ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply e.hom.val f.op s).symm

lemma component_restrict {U V : X.Opens} (e : A.over U ≅ B.over U) (h : V ≤ U)
    (W : X.Opens) (hW : W ≤ V) (s : Γ(A,W)) :
    component (restrictIso e h) W hW s = component e W (hW.trans h) s := rfl

variable {ι : Type u} (U : ι → X.Opens) (M : ι → X.Modules)
/-- Genuine sheaf overlap isomorphisms on the original pairwise opens.
Only their original identity and triple-overlap cocycle are supplied;
all-subopen scalar comparisons and naturality will be derived. -/
structure Data where
  transition : ∀ i j, (M i).over (U i ⊓ U j) ≅ (M j).over (U i ⊓ U j)
  identity : ∀ i, transition i i = Iso.refl _
  cocycle : ∀ i j k,
    restrictIso (transition i j) (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) ≪≫
      restrictIso (transition j k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    restrictIso (transition i k)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

variable {U M} (D : Data U M)
/-- The actual sheaf overlap data supplies every linear common-subopen
transition, with its naturality and identity/cocycle derived rather than added. -/
@[expose] def sectionData : OpenModuleTransition318.Data U M where
  transition i j V hi hj := component (D.transition i j) V (le_inf hi hj)
  natural i j V W hi hj h s := component_natural (D.transition i j) V W (le_inf hi hj) h s
  identity i V hi s := by
    change component (D.transition i i) V (le_inf hi hi) s = s
    rw [D.identity]
    rfl
  cocycle i j k V hi hj hk s := by
    have h := congrArg (fun e => component e V (le_inf (le_inf hi hj) hk) s) (D.cocycle i j k)
    change component (restrictIso (D.transition j k) _) V _
        (component (restrictIso (D.transition i j) _) V _ s) =
      component (restrictIso (D.transition i k) _) V _ s at h
    simpa only [component_restrict] using h
end OpenSheafTransition318
