module

public import SelectedSameAPrincipalUnitMarkedFrame318
public import SelectedSameAConstantPrincipalLine318
public import StructurePushforwardSplit318
public import ModuleFrameDescent318

/-!
Produce both canonical arrows on the actual pushed-forward
normalized line; derive the overlap difference in that very
module. The line is an actual presented module on A_D, not a
reconstructed line or an input short complex.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitPushforwardArrows318

open SelectedSameAActualNilpotentLineGluing318
open SelectedSameAConstantPrincipalLine318
open SelectedSameAPrincipalUnitMarkedFrame318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k]
variable {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
variable {I : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (hc : (⊤ : A.Opens) ≤ ⨆ i, U i)

abbrev projection := pullback.fst a (base k)
abbrev red := reducedConstant a
abbrev unit (Y : Scheme.{u}) := SheafOfModules.unit Y.ringCatSheaf

theorem reduction_projects : red a ≫ projection a = 𝟙 A :=
  pullback.lift_fst _ _ _

abbrev V := pre (projection a) U

variable (M : (constantScheme a).Modules)
variable (f : ∀ j, unit ((V a U j).toScheme) ≅ M.restrict (V a U j).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (markedEpsilon a) (markedEpsilon_sq a) (constantCocycle a U c))

abbrev middle : A.Modules := (Scheme.Modules.pushforward (projection a)).obj M

/-- The actual epsilon-times-frame section of the given normalized
line. It globalizes the same local sections in the actual frames. -/
@[expose] def epsilonMap : unit (constantScheme a) ⟶ M :=
  ModuleGlobalSections318.gluedMap M (V a U) (preCover (projection a) U hc)
    (epsGen (V a U) M f (markedEpsilon a))
    (eps_compatible (V a U) M f (markedEpsilon a) (markedEpsilon_sq a)
      (constantCocycle a U c) hframe)

/-- Kernel arrow over A built from the actual global epsilon frame. -/
@[expose] def left : unit A ⟶ middle a M :=
  StructurePushforwardSplit318.unitMap (projection a) ≫
    (Scheme.Modules.pushforward (projection a)).map (epsilonMap a U c hc M f hframe)

variable (fibreFrame : (Scheme.Modules.pullback (red a)).obj M ≅ unit A)

/-- Actual reduced frame, adjointed along the literal closed-fibre
map into the same module before restriction of scalars. -/
@[expose] def reduceToPushforward :
    M ⟶ (Scheme.Modules.pushforward (red a)).obj (unit A) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (red a)).homEquiv _ _ fibreFrame.hom

/-- The reduction of the actual pushed-forward line uses precisely
the functorial identity of the given projection and closed point. -/
@[expose] def right : middle a M ⟶ unit A :=
  (Scheme.Modules.pushforward (projection a)).map (reduceToPushforward a M fibreFrame) ≫
    (Scheme.Modules.pushforwardComp (red a) (projection a)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (reduction_projects a)).hom.app _ ≫
    (Scheme.Modules.pushforwardId A).hom.app _

/-- The actual local unit-frame lift, now in the sheaf on A. -/
@[expose] def generator (j : I) : Γ(middle a M,U j) :=
  gen (V a U) M f j

include hframe hc in
/-- On any subopen of a true chart the actual injection is multiplication
by the same marked epsilon in the actual first frame. -/
theorem left_chart (j : I) (W : A.Opens) (hW : W ≤ U j) (b : Γ(A,W)) :
    Scheme.Modules.Hom.app (left a U c hc M f hframe) W b =
      OpenLineFrameCoordinates318.frame M (V a U j) (f j)
        ((projection a) ⁻¹ᵁ W) ((projection a).preimage_mono hW)
        (epsilonOn (markedEpsilon a) ((projection a) ⁻¹ᵁ W) * ((projection a).app W b)) := by
  let q := projection a
  let V' := V a U
  let e := markedEpsilon a
  let W' := q ⁻¹ᵁ W
  let hW' : W' ≤ V' j := q.preimage_mono hW
  let s := epsGen V' M f e
  let hs := eps_compatible V' M f e (markedEpsilon_sq a) (constantCocycle a U c) hframe
  have ht := ModuleFrameDescent318.gluedMap_on_subopen
    (M := M) V' (preCover q U hc) s hs j W' hW' (q.app W b)
  change (epsilonMap a U c hc M f hframe).val.app (op W') (q.app W b) =
    q.app W b • M.presheaf.map (homOfLE hW').op (s j) at ht
  unfold left
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
  change (epsilonMap a U c hc M f hframe).val.app (op W') (q.app W b) = _
  refine ht.trans ?_
  have hR := OpenLineFrameCoordinates318.natural M (V' j) (f j) le_rfl hW'
    (epsilonOn e (V' j))
  change M.presheaf.map (homOfLE hW').op (s j) =
    OpenLineFrameCoordinates318.frame (X := constantScheme a) M (V' j) (f j) W' hW'
      ((constantScheme a).presheaf.map (homOfLE hW').op (epsilonOn e (V' j))) at hR
  have he := epsilonOn_restrict e hW'
  change (constantScheme a).presheaf.map (homOfLE hW').op (epsilonOn e (V' j)) =
    epsilonOn e W' at he
  rw [hR, he, ← LinearEquiv.map_smul, smul_eq_mul, mul_comm (q.app W b)]

include hframe hc in
/-- The actual right-minus-left frame difference, on the true
inverse image of the entire original overlap. -/
theorem pushed_signed_difference (i j : I) :
    (middle a M).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
        (generator a U M f j) -
      (middle a M).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
        (generator a U M f i) =
      Scheme.Modules.Hom.app (left a U c hc M f hframe) (U i ⊓ U j) (c.coeff i j) := by
  let q := projection a
  let W := U i ⊓ U j
  let W' : (constantScheme a).Opens := q ⁻¹ᵁ W
  have hWi : W' ≤ V a U i :=
    q.preimage_mono (show W ≤ U i from inf_le_left)
  have hWj : W' ≤ V a U j :=
    q.preimage_mono (show W ≤ U j from inf_le_right)
  have hd := signed_difference (V a U) M f (markedEpsilon a)
    (markedEpsilon_sq a) (constantCocycle a U c) hframe i j
  change M.presheaf.map (homOfLE hWj).op
        (gen (V a U) M f j) -
      M.presheaf.map (homOfLE hWi).op
        (gen (V a U) M f i) =
      Scheme.Modules.Hom.app (left a U c hc M f hframe) W (c.coeff i j)
  refine hd.trans ?_
  have hp : (constantCocycle a U c).coeff i j = q.app W (c.coeff i j) := by
    change q.appLE W W' le_rfl (c.coeff i j) = q.app W (c.coeff i j)
    rw [Scheme.Hom.app_eq_appLE]
  rw [hp]
  exact (left_chart a U c hc M f hframe i W inf_le_left (c.coeff i j)).symm

end SelectedSameAPrincipalUnitPushforwardArrows318
