module

public import SelectedSameAPrincipalUnitActualReduction318
public import SelectedSameAPrincipalUnitAffineReduction318
public import SelectedSameAActualConstantAffineCoefficients318

/-!
At a genuine affine inside one normalized line frame, the actual global
epsilon arrow and the actual glued reduction have the literal inr and
fst coefficients. All scalar identities come from the same actual
constant base-change chart, not separately calibrated arrows.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitActualAffineArrows318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SelectedSameAActualNilpotentLineGluing318
open SelectedSameAPrincipalUnitPushforwardArrows318
open SelectedSameAPrincipalUnitActualReduction318
open SelectedSameAActualConstantAffineCoefficients318
open SelectedSameAConstantTargetTriangle318 (sp)
open SelectedSameAActualAffineOpenCoefficientIso318 (coordinate)

variable {k : Type u} [Field k] {A : Scheme.{u}}
variable (a : A ⟶ Spec (CommRingCat.of k))
variable {B : Type u} [CommRing B] [Algebra k B]
variable (j : Spec (CommRingCat.of B) ⟶ A) [IsOpenImmersion j]
variable (hj : j ≫ a = sp (algebraMap k B))

abbrev W := originalOpen j
abbrev WD := constantOpen a j

/-- The actual coefficient in B uses the literal original affine
inclusion and the fixed canonical ΓSpec, not an arbitrary ring iso. -/
abbrev baseCoordinate (z : Γ(A,W j)) : B := coordinate j (W j) rfl z

abbrev dualCoordinate (z : Γ(SelectedSameAConstantPrincipalLine318.constantScheme a,WD a j)) :
    TrivSqZeroExt B B :=
  (actualCoordinateIso a j hj).hom z

/-- The two existing closed-reduction constructions are the same
marked global morphism (only their commutativity proofs differ). -/
theorem red_is_constantReduction :
    red a = SelectedSameAConstantActualReduction318.constantReduction a := by
  apply pullback.hom_ext
  · exact (reduction_projects a).trans
      (SelectedSameAConstantActualReduction318.constantReduction_fst a).symm
  · rw [SelectedSameAConstantActualReduction318.constantReduction_snd]
    exact pullback.lift_snd _ _ _

include hj in
theorem constant_beta (z : Γ(A,W j)) :
    dualCoordinate a j hj ((projection a).app (W j) z) =
      (TrivSqZeroExt.inl (baseCoordinate j z) : TrivSqZeroExt B B) := by
  have h := congrArg (fun f : Γ(A,W j) ⟶ CommRingCat.of (TrivSqZeroExt B B) => f z)
    (constant_coefficient a j hj)
  exact h

include hj in
theorem reduction_beta
    (z : Γ(SelectedSameAConstantPrincipalLine318.constantScheme a,WD a j)) :
    baseCoordinate j (reduction a (W j) z) =
      (dualCoordinate a j hj z).fst := by
  have hr := closed_coefficient a j hj
  have h := congrArg (fun g :
      Γ(SelectedSameAConstantPrincipalLine318.constantScheme a,WD a j) ⟶
        CommRingCat.of B => g z) hr
  refine Eq.trans ?_ h
  unfold reduction baseCoordinate
  have hSame := red_is_constantReduction a
  have hApp := AffineChartPullbackScalars318.appLE_congr_map hSame
    (WD a j) (W j) (preRed a (W j)) (preimage_constantOpen a j).ge
  exact congrArg (fun g : Γ(SelectedSameAConstantPrincipalLine318.constantScheme a,WD a j) ⟶
      Γ(A,W j) => coordinate j (W j) rfl (g z)) hApp

include hj in
theorem marked_beta :
    dualCoordinate a j hj (epsilonOn (SelectedSameAConstantPrincipalLine318.markedEpsilon a) (WD a j)) =
      (TrivSqZeroExt.inr (1 : B) : TrivSqZeroExt B B) := by
  let p := pullback.snd a (SelectedSameAConstantPrincipalLine318.base k)
  let e := (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt k k))).inv
    (TrivSqZeroExt.inr (1 : k))
  have h : p.appTop ≫
      (SelectedSameAConstantPrincipalLine318.constantScheme a).presheaf.map
        (homOfLE (show WD a j ≤ ⊤ from le_top)).op =
      p.appLE ⊤ (WD a j) le_top := by
    change p.app ⊤ ≫ _ = _
    rw [p.app_eq_appLE, Scheme.Hom.appLE_map]
  have he := congrArg (fun m => m e) h
  change epsilonOn (SelectedSameAConstantPrincipalLine318.markedEpsilon a) (WD a j) =
    p.appLE ⊤ (WD a j) le_top e at he
  rw [he]
  exact marked_epsilon_coefficient a j hj

variable {I : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (hc : (⊤ : A.Opens) ≤ ⨆ i, U i)
variable (M : (SelectedSameAConstantPrincipalLine318.constantScheme a).Modules)
variable (f : ∀ i, unit ((V a U i).toScheme) ≅ M.restrict (V a U i).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (SelectedSameAConstantPrincipalLine318.markedEpsilon a)
    (SelectedSameAConstantPrincipalLine318.markedEpsilon_sq a)
    (SelectedSameAConstantPrincipalLine318.constantCocycle a U c))
variable (i : I) (hW : W j ≤ U i)

abbrev coefficient (s : Γ(middle a M,W j)) : TrivSqZeroExt B B :=
  dualCoordinate a j hj ((coor a U M f i (W j) hW).symm s)

/-- Both equalities are evaluated in the *same* actual module and frame.
The left arrow sends b to the marked inr coefficient of the original b. -/
theorem left_inr (b : Γ(A,W j)) :
    coefficient a j hj U M f i hW ((left a U c hc M f hframe).app (W j) b) =
      TrivSqZeroExt.inr (baseCoordinate j b) := by
  unfold coefficient
  rw [left_chart a U c hc M f hframe i (W j) hW]
  change dualCoordinate a j hj ((coor a U M f i (W j) hW).symm
    ((coor a U M f i (W j) hW)
      (epsilonOn (SelectedSameAConstantPrincipalLine318.markedEpsilon a) (WD a j) *
        ((projection a).app (W j) b)))) = _
  rw [LinearEquiv.symm_apply_apply]
  change (actualCoordinateIso a j hj).hom
      (epsilonOn (SelectedSameAConstantPrincipalLine318.markedEpsilon a) (WD a j) *
        ((projection a).app (W j) b)) = _
  rw [map_mul]
  change dualCoordinate a j hj (epsilonOn (SelectedSameAConstantPrincipalLine318.markedEpsilon a)
    (WD a j)) * dualCoordinate a j hj ((projection a).app (W j) b) = _
  rw [marked_beta a j hj, constant_beta a j hj]
  exact SelectedSameAPrincipalUnitAffineReduction318.epsilon_mul_lift B (baseCoordinate j b)

/-- The actual glued right arrow reads precisely the reduction
coefficient in the very same marked frame coordinates. -/
theorem right_fst (s : Γ(middle a M,W j)) :
    baseCoordinate j ((readReduction a U c M f hframe hc).app (W j) s) =
      (coefficient a j hj U M f i hW s).fst := by
  rw [on_chart a U c M f hframe hc i (W j) hW]
  exact reduction_beta a j hj ((coor a U M f i (W j) hW).symm s)

end SelectedSameAPrincipalUnitActualAffineArrows318
