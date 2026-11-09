module
public import ScalarExtensionComposition318
public import AffineOverlapDiagonal318
public section
noncomputable section
namespace AffineDiagonalPullback318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open AffineOverlapDiagonal318 ScalarExtensionComposition318
open scoped ChangeOfRings
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)

@[expose] def firstIso :
    (ModuleCat.extendScalars (diagonal R S).hom).obj (first R S N) ≅ N :=
  splitIso (leftMap R S S).hom (diagonal R S).hom (diagonal_left R S) N
@[expose] def secondIso :
    (ModuleCat.extendScalars (diagonal R S).hom).obj (second R S N) ≅ N :=
  splitIso (rightMap R S S).hom (diagonal R S).hom (diagonal_right R S) N

lemma firstIso_adjoint :
    (ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _
      (firstIso R S N).hom = firstEvaluation R S N := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, firstEvaluation_unit]
  change (splitIso _ _ _ N).hom
    ((1 : S) ⊗ₜ[ring R S S, (diagonal R S).hom]
      ((1 : S ⊗[R] S) ⊗ₜ[S, (leftMap R S S).hom] n)) = n
  rw [splitIso_hom_tmul]
  simp

lemma secondIso_adjoint :
    (ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _
      (secondIso R S N).hom = secondEvaluation R S N := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change (splitIso _ _ _ N).hom
    ((1 : S) ⊗ₜ[ring R S S, (diagonal R S).hom]
      ((1 : S ⊗[R] S) ⊗ₜ[S, (rightMap R S S).hom] n)) = _
  rw [splitIso_hom_tmul]
  simp only [map_one, mul_one, one_smul]
  change n = ((ModuleCat.extendRestrictScalarsAdj (rightMap R S S).hom).homEquiv _ _
    (secondEvaluation R S N)) n
  rw [secondEvaluation, Equiv.apply_symm_apply]
  rfl

/-- Normalization on the actual diagonal scalar pullback gives exactly
the original evaluation equation, hence the genuine comonad counit. -/
lemma counit_of_pullback_identity (a : first R S N ⟶ second R S N)
    (ha : (firstIso R S N).inv ≫ (ModuleCat.extendScalars (diagonal R S).hom).map a ≫
      (secondIso R S N).hom = 𝟙 N) :
    AffineOverlapCoaction318.homEquiv R S N a ≫
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).counit.app N = 𝟙 N := by
  apply counit_of_diagonal
  have h : (ModuleCat.extendScalars (diagonal R S).hom).map a ≫
      (secondIso R S N).hom = (firstIso R S N).hom := by
    apply (cancel_epi (firstIso R S N).inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id] using ha
  have k := congrArg
    ((ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _) h
  rw [Adjunction.homEquiv_naturality_left, firstIso_adjoint, secondIso_adjoint] at k
  exact k
end AffineDiagonalPullback318
