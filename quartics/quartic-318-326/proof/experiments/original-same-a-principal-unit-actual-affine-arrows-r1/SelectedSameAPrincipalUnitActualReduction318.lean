module

public import SelectedSameAPrincipalUnitPushforwardArrows318
public import ModuleLocalGluing318

/-!
The actual right arrow is read directly in the same normalized
frames. It uses the literal closed immersions' ring maps;
compatibility follows because the principal transitions reduce
to one. No global reduction map or lift of one is assumed.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitActualReduction318
open SelectedSameAActualNilpotentLineGluing318
open SelectedSameAConstantPrincipalLine318
open SelectedSameAPrincipalUnitPushforwardArrows318
open SelectedSameAPrincipalUnitMarkedFrame318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k]
variable {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

theorem preRed (W : A.Opens) : W ≤ (red a) ⁻¹ᵁ ((projection a) ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, reduction_projects a, Scheme.Hom.id_preimage]

/-- Literal direct ring reduction on any actual pushforward open. -/
@[expose] def reduction (W : A.Opens) : Γ(constantScheme a,(projection a) ⁻¹ᵁ W) ⟶ Γ(A,W) :=
  (red a).appLE _ W (preRed a W)

theorem projection_reduction (W : A.Opens) : (projection a).app W ≫ reduction a W = 𝟙 _ := by
  unfold reduction
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have hident (f : A ⟶ A) (hf : f = 𝟙 A) (h : W ≤ f ⁻¹ᵁ W) :
      f.appLE W W h = 𝟙 _ := by
    subst f
    simp [Scheme.Hom.appLE]
    exact A.presheaf.map_id _
  exact hident _ (reduction_projects a) _

theorem reduction_on_constant (W : A.Opens) (b : Γ(A,W)) :
    reduction a W ((projection a).app W b) = b := by
  have H := congrArg (fun f : Γ(A,W) ⟶ Γ(A,W) => f b) (projection_reduction a W)
  exact H

abbrev openPull {W Z : A.Opens} (h : Z ≤ W) :
    (projection a) ⁻¹ᵁ Z ≤ (projection a) ⁻¹ᵁ W :=
  (projection a).preimage_mono h

theorem reduction_natural {W Z : A.Opens} (h : Z ≤ W)
    (b : Γ(constantScheme a,(projection a) ⁻¹ᵁ W)) :
    A.presheaf.map (homOfLE h).op (reduction a W b) =
      reduction a Z ((constantScheme a).presheaf.map (homOfLE (openPull a h)).op b) := by
  have hterm : reduction a W ≫ A.presheaf.map (homOfLE h).op =
      (constantScheme a).presheaf.map (homOfLE (openPull a h)).op ≫ reduction a Z := by
    unfold reduction
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun f => f b) hterm

theorem reduction_epsilon (W : A.Opens) :
    reduction a W (epsilonOn (markedEpsilon a) ((projection a) ⁻¹ᵁ W)) = 0 := by
  let r := red a
  let Z := (projection a) ⁻¹ᵁ W
  have h : (constantScheme a).presheaf.map (homOfLE (show Z ≤ ⊤ from le_top)).op ≫ reduction a W =
      r.appTop ≫ A.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op := by
    unfold reduction
    change _ = r.app (⊤ : (constantScheme a).Opens) ≫ _
    rw [r.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have e := congrArg (fun f => f (markedEpsilon a)) h
  change reduction a W (epsilonOn (markedEpsilon a) Z) =
    A.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (r.appTop (markedEpsilon a)) at e
  exact e.trans (by rw [markedEpsilon_killed, map_zero])

variable {I : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (M : (constantScheme a).Modules)
variable (f : ∀ j, unit ((V a U j).toScheme) ≅ M.restrict (V a U j).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (markedEpsilon a) (markedEpsilon_sq a) (constantCocycle a U c))

abbrev coor (i : I) (W : A.Opens) (h : W ≤ U i) :=
  OpenLineFrameCoordinates318.frame M (V a U i) (f i) ((projection a) ⁻¹ᵁ W) (openPull a h)

@[expose] def localRight (i : I) (W : A.Opens) (h : W ≤ U i) :
    Γ(middle a M,W) →ₗ[Γ(A,W)] Γ(unit A,W) where
  toFun z := reduction a W ((coor a U M f i W h).symm z)
  map_add' x y := by rw [map_add, map_add]
  map_smul' b z := by
    change reduction a W ((coor a U M f i W h).symm ((projection a).app W b •
      (show Γ(M,(projection a) ⁻¹ᵁ W) from z))) =
        b * reduction a W ((coor a U M f i W h).symm z)
    rw [LinearEquiv.map_smul, smul_eq_mul, map_mul, reduction_on_constant]

include hframe

private theorem transition_reduces (i j : I) (W : A.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    reduction a W
      (LineFrameTransitions318.scalar M (V a U) f i j ((projection a) ⁻¹ᵁ W)
        (openPull a hi) (openPull a hj)).val = 1 := by
  let h := le_inf (openPull a hi) (openPull a hj)
  have H := congrArg Units.val
    (LineFrameTransitions318.restrict M (V a U) f i j inf_le_left inf_le_right h)
  change (constantScheme a).presheaf.map (homOfLE h).op
    ((LineFrameCocycle318.cocycle M (V a U) f).transition i j).val = _ at H
  rw [hframe] at H
  change (constantScheme a).presheaf.map (homOfLE h).op
    (nilUnit _ _ ((constantCocycle a U c).coeff i j)).val = _ at H
  rw [nilUnit_val, map_add, map_one, map_mul] at H
  have he := epsilonOn_restrict (markedEpsilon a) h
  change (constantScheme a).presheaf.map (homOfLE h).op
    (epsilonOn (markedEpsilon a) (V a U i ⊓ V a U j)) =
      epsilonOn (markedEpsilon a) ((projection a) ⁻¹ᵁ W) at he
  rw [← H, he, map_add, map_one, map_mul, reduction_epsilon, zero_mul, add_zero]

/-- Genuine local coefficient reductions descend by the structure
sheaf's actual restriction maps; no nonflat tensor of a global
equalizer is used. -/
@[expose] def localData : ModuleLocalGluing318.LocalData (middle a M) (unit A) U where
  map i W h := localRight a U M f i W h
  natural i W Z hW hZ z := by
    change A.presheaf.map (homOfLE hZ).op
      (reduction a W ((coor a U M f i W hW).symm z)) =
      reduction a Z ((coor a U M f i Z (hZ.trans hW)).symm
        (M.presheaf.map (homOfLE (openPull a hZ)).op z))
    rw [reduction_natural, OpenLineFrameCoordinates318.inverse_natural]
  compatible i j W hi hj z := by
    let g := LineFrameTransitions318.scalar M (V a U) f i j ((projection a) ⁻¹ᵁ W)
      (openPull a hi) (openPull a hj)
    have H := LineFrameTransitions318.relation M (V a U) f i j ((projection a) ⁻¹ᵁ W)
      (openPull a hi) (openPull a hj) ((coor a U M f j W hj).symm z)
    change (coor a U M f i W hi) (g.val * (coor a U M f j W hj).symm z) =
      (coor a U M f j W hj) ((coor a U M f j W hj).symm z) at H
    rw [LinearEquiv.apply_symm_apply] at H
    have H' := congrArg (coor a U M f i W hi).symm H
    rw [LinearEquiv.symm_apply_apply] at H'
    change reduction a W ((coor a U M f i W hi).symm z) =
      reduction a W ((coor a U M f j W hj).symm z)
    rw [← H', map_mul, transition_reduces a U c M f hframe i j W hi hj, one_mul]

variable (hc : (⊤ : A.Opens) ≤ ⨆ j, U j)

/-- This is the literal reduction of the frame coefficients of
the actual pushed-forward line into the fixed trivial frame. -/
@[expose] def readReduction : middle a M ⟶ unit A :=
  ModuleLocalGluing318.hom (localData a U c M f hframe) hc

theorem on_chart (i : I) (W : A.Opens) (hW : W ≤ U i) (s : Γ(middle a M,W)) :
    (readReduction a U c M f hframe hc).app W s =
      reduction a W ((coor a U M f i W hW).symm s) := by
  change ModuleLocalGluing318.value (localData a U c M f hframe) hc W s = _
  have h := ModuleLocalGluing318.value_subopen (localData a U c M f hframe) hc W W
    le_rfl i hW s
  rw [ModuleLocalGluing318.res_self, ModuleLocalGluing318.res_self] at h
  exact h

theorem generator_lifts_one (i : I) :
    (readReduction a U c M f hframe hc).app (U i) (generator a U M f i) =
      (1 : Γ(A,U i)) := by
  rw [on_chart a U c M f hframe hc i (U i) le_rfl]
  change reduction a (U i) ((coor a U M f i (U i) le_rfl).symm
    ((coor a U M f i (U i) le_rfl) 1)) = 1
  rw [LinearEquiv.symm_apply_apply, map_one]

end SelectedSameAPrincipalUnitActualReduction318
