module
public import AffineOverlapCoaction318
public section
noncomputable section
namespace AffineOverlapDiagonal318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open scoped ChangeOfRings
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)
abbrev diagonal : ring R S S ⟶ S :=
  CommRingCat.ofHom (Algebra.TensorProduct.lmul' R).toRingHom

lemma diagonal_left : (diagonal R S).hom.comp (leftMap R S S).hom = RingHom.id S := by
  ext s
  exact mul_one s
lemma diagonal_right : (diagonal R S).hom.comp (rightMap R S S).hom = RingHom.id S := by
  ext s
  exact one_mul s

/-- The original module map evaluating the first overlap pullback on the
actual diagonal. It is obtained from the original adjunction and the
proved diagonal composite, with no new action on N. -/
@[expose] def firstEvaluation : first R S N ⟶
    (ModuleCat.restrictScalars (diagonal R S).hom).obj N :=
  ((ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv _ _).symm
    (((ModuleCat.restrictScalarsId S).inv.app N) ≫
      (ModuleCat.restrictScalarsComp' (leftMap R S S).hom (diagonal R S).hom
        (RingHom.id S) (diagonal_left R S).symm).hom.app N)

@[expose] def secondEvaluation : second R S N ⟶
    (ModuleCat.restrictScalars (diagonal R S).hom).obj N :=
  ((ModuleCat.extendRestrictScalarsAdj (rightMap R S S).hom).homEquiv _ _).symm
    (((ModuleCat.restrictScalarsId S).inv.app N) ≫
      (ModuleCat.restrictScalarsComp' (rightMap R S S).hom (diagonal R S).hom
        (RingHom.id S) (diagonal_right R S).symm).hom.app N)

lemma firstEvaluation_unit (n : N) :
    firstEvaluation R S N ((1 : S ⊗[R] S) ⊗ₜ[S, (leftMap R S S).hom] n) = n := by
  change ((ModuleCat.extendRestrictScalarsAdj (leftMap R S S).hom).homEquiv _ _
    (firstEvaluation R S N)) n = n
  rw [firstEvaluation, Equiv.apply_symm_apply]
  rfl

/-- The original comonad counit after the original pushout comparison is
exactly evaluation of the second overlap module on the actual diagonal. -/
lemma counit_component (z : second R S N) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).counit.app N
      ((component R S S N).hom z) = secondEvaluation R S N z := by
  change ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).counit.app N).hom
    ((component R S S N).hom.hom z) = (secondEvaluation R S N).hom z
  induction z using TensorProduct.inductionOn with
  | tmul t n =>
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
          change a • (b • n) = (a * b) • n
          exact (mul_smul a b n).symm
      | add t s ht hs => simp only [add_tmul, map_add, ht, hs]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Actual normalized overlap evaluation implies the actual comonad
counit equation for its candidate coaction. Triple-overlap coassociativity
is not supplied by this diagonal argument. -/
lemma counit_of_diagonal (a : first R S N ⟶ second R S N)
    (ha : a ≫ secondEvaluation R S N = firstEvaluation R S N) :
    AffineOverlapCoaction318.homEquiv R S N a ≫
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).counit.app N = 𝟙 N := by
  ext n
  change (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).counit.app N
    (AffineOverlapCoaction318.homEquiv R S N a n) = n
  rw [homEquiv_value, counit_component]
  have h := congrArg (fun k : first R S N ⟶
    (ModuleCat.restrictScalars (diagonal R S).hom).obj N =>
      k ((1 : S ⊗[R] S) ⊗ₜ[S, (leftMap R S S).hom] n)) ha
  exact h.trans (firstEvaluation_unit R S N n)
end AffineOverlapDiagonal318
