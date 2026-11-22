module

public import SelectedSameAPrincipalUnitActualReduction318
public import SelectedActualAdditiveStalkLocalExact318
public import SelectedSameAGenuineBoundaryLifts318
public import SelectedSameASignedLiftCocycle318
import all SelectedSameAPrincipalUnitActualReduction318

/-!
A literal reduction complex of the actual normalized line, with its
own signed generators over the same cover. Its application to the
derived additive boundary is stated separately from the unassembled
affine splitting of the scheme restrictions.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitBoundary318

open SelectedSameAActualNilpotentLineGluing318
open SelectedSameAConstantPrincipalLine318
open SelectedSameAPrincipalUnitPushforwardArrows318
open SelectedSameAPrincipalUnitActualReduction318
open SelectedActualAdditiveStalkLocalExact318

universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k]
variable {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
variable {I : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (hc : (⊤ : A.Opens) ≤ ⨆ i, U i)
variable (M : (constantScheme a).Modules)
variable (f : ∀ j, unit ((V a U j).toScheme) ≅ M.restrict (V a U j).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (markedEpsilon a) (markedEpsilon_sq a) (constantCocycle a U c))

abbrev j := left a U c hc M f hframe
abbrev g := readReduction a U c M f hframe hc

theorem zero_on_chart (i : I) (W : A.Opens) (hW : W ≤ U i) (b : Γ(A,W)) :
    (g a U c hc M f hframe).app W ((j a U c hc M f hframe).app W b) = 0 := by
  rw [on_chart a U c M f hframe hc i W hW, left_chart a U c hc M f hframe i W hW]
  change reduction a W ((coor a U M f i W hW).symm
    ((coor a U M f i W hW) (epsilonOn (markedEpsilon a) ((projection a) ⁻¹ᵁ W) *
      ((projection a).app W b)))) = 0
  rw [LinearEquiv.symm_apply_apply, map_mul, reduction_epsilon, zero_mul]

theorem actual_zero : j a U c hc M f hframe ≫ g a U c hc M f hframe = 0 := by
  let t := j a U c hc M f hframe ≫ g a U c hc M f hframe
  apply Scheme.Modules.hom_ext
  intro W
  ext b
  change t.app W b = (0 : unit A ⟶ unit A).app W b
  rw [Scheme.Modules.Hom.zero_app]
  change t.app W b = (0 : Γ(A,W))
  apply ModuleLocalGluing318.ext_value (N := unit A) (U := U) hc W
  intro i
  let d : W ⊓ U i ≤ W := inf_le_left
  let R := A.presheaf.map (homOfLE d).op
  have hn := congrArg (fun m => m b) (t.mapPresheaf.naturality (homOfLE d).op)
  change t.app (W ⊓ U i) (R b) = R (t.app W b) at hn
  change R (t.app W b) = R 0
  rw [← hn, map_zero]
  change ((j a U c hc M f hframe ≫ g a U c hc M f hframe).app (W ⊓ U i)) (R b) = 0
  rw [Scheme.Modules.Hom.comp_app]
  exact zero_on_chart a U c hc M f hframe i (W ⊓ U i) inf_le_right (R b)

/-- The original pushed-forward line with the actual epsilon arrow
and actual reduced-frame projection. -/
@[expose] def row : ShortComplex A.Modules :=
  ShortComplex.mk (j a U c hc M f hframe) (g a U c hc M f hframe)
    (actual_zero a U c hc M f hframe)

abbrev additive := additiveRow (row a U c hc M f hframe)
abbrev X : TopCat.{u} := (A : TopCat.{u})

variable [HasSheafify (_root_.Opens.grothendieckTopology (X (A := A))) AddCommGrpCat.{u}]

abbrev one : (additive a U c hc M f hframe).X₃.obj.obj
      (op (⊤ : A.Opens)) := (1 : Γ(A,⊤))

abbrev lift (i : I) : (additive a U c hc M f hframe).X₂.obj.obj
    (op (U i)) := generator a U M f i

theorem genuine_lift (i : I) :
    (additive a U c hc M f hframe).g.hom.app (op (U i))
        (lift a U c hc M f hframe i) =
      SelectedSameASignedLiftCocycle318.res (X (A := A))
        (additive a U c hc M f hframe).X₃ le_top (one a U c hc M f hframe) := by
  change (g a U c hc M f hframe).app (U i) (generator a U M f i) =
    A.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (1 : Γ(A,⊤))
  rw [generator_lifts_one, map_one]

variable (hExact : (additive a U c hc M f hframe).ShortExact)

/-- Whenever the affine chart splittings have been assembled for this
literal row, the already constructed lifts read exactly its original
signed coefficient, without a comparison to the old KS extension. -/
theorem coefficient (i j' : I) :
    SelectedSameASignedLiftCocycle318.coeff (X (A := A)) (additive a U c hc M f hframe)
      hExact U (one a U c hc M f hframe) (lift a U c hc M f hframe)
      (genuine_lift a U c hc M f hframe) i j' =
        (show (additive a U c hc M f hframe).X₁.obj.obj (op (U i ⊓ U j')) from c.coeff i j') := by
  apply SelectedSameAActualLiftDifference318.local_inclusion_injective (X (A := A))
    (additive a U c hc M f hframe) hExact (U i ⊓ U j')
  rw [SelectedSameASignedLiftCocycle318.coeff_beta]
  change (middle a M).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j' ≤ U j')).op
      (generator a U M f j') -
    (middle a M).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j' ≤ U i)).op
      (generator a U M f i) = (j a U c hc M f hframe).app (U i ⊓ U j') (c.coeff i j')
  exact pushed_signed_difference a U c hc M f hframe i j'

variable [HasExt.{w} (Sheaf (_root_.Opens.grothendieckTopology (X (A := A))) AddCommGrpCat.{u})]

/-- Forward normalized principal-unit class, the genuine additive
boundary of one from this line's reduction row. -/
@[expose] def onOne : (additive a U c hc M f hframe).X₁.H 1 :=
  SelectedSameAGenuineBoundaryLifts318.boundary (X (A := A)) hExact
    (one a U c hc M f hframe)

end SelectedSameAPrincipalUnitBoundary318
