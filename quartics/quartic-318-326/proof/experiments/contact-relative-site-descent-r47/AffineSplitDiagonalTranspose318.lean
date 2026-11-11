module
public import OriginalGeometricDiagonal318
public section
noncomputable section
namespace AffineSplitDiagonalTranspose318
open CategoryTheory AlgebraicGeometry TensorProduct LineSheafClass318 AffineModuleBaseChange318
open AffineOverlapDiagonal318
open scoped ChangeOfRings
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat S)

lemma secondEvaluation_unit (n : N) :
    secondEvaluation R S N ((1 : S ⊗[R] S) ⊗ₜ[S, (rightMap R S S).hom] n) = n := by
  change ((ModuleCat.extendRestrictScalarsAdj (rightMap R S S).hom).homEquiv _ _
    (secondEvaluation R S N)) n = n
  rw [secondEvaluation, Equiv.apply_symm_apply]
  rfl

lemma first_transpose :
    (ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _
      (ScalarExtensionComposition318.splitIso (leftMap R S S).hom (diagonal R S).hom
        (diagonal_left R S) N).hom = firstEvaluation R S N := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change (ScalarExtensionComposition318.splitIso (leftMap R S S).hom (diagonal R S).hom
    (diagonal_left R S) N).hom
    ((1 : S) ⊗ₜ[ring R S S, (diagonal R S).hom]
      ((1 : S ⊗[R] S) ⊗ₜ[S, (leftMap R S S).hom] n)) = _
  rw [ScalarExtensionComposition318.splitIso_hom_tmul, firstEvaluation_unit]
  simp only [map_one, mul_one, one_smul]

lemma second_transpose :
    (ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _
      (ScalarExtensionComposition318.splitIso (rightMap R S S).hom (diagonal R S).hom
        (diagonal_right R S) N).hom = secondEvaluation R S N := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change (ScalarExtensionComposition318.splitIso (rightMap R S S).hom (diagonal R S).hom
    (diagonal_right R S) N).hom
    ((1 : S) ⊗ₜ[ring R S S, (diagonal R S).hom]
      ((1 : S ⊗[R] S) ⊗ₜ[S, (rightMap R S S).hom] n)) = _
  rw [ScalarExtensionComposition318.splitIso_hom_tmul, secondEvaluation_unit]
  simp only [map_one, mul_one, one_smul]

/-- The actual geometric diagonal identity yields exactly the module
evaluation identity required by the original counit proof. -/
lemma diagonal_to_module (L : Line (Spec S))
    (τ : OriginalLineOverlapCoaction318.first R S L ⟶
      OriginalLineOverlapCoaction318.second R S L)
    (hτ : OriginalGeometricDiagonal318.Diagonal R S L τ) :
    OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ ≫
        secondEvaluation R S (OriginalLineAffineModel318.sections S L) =
      firstEvaluation R S (OriginalLineAffineModel318.sections S L) := by
  have h := congrArg ((ModuleCat.extendRestrictScalarsAdj (diagonal R S).hom).homEquiv _ _)
    (OriginalGeometricDiagonal318.diagonal_to_split R S L τ hτ)
  simpa only [OriginalGeometricDiagonal318.diagonal, OriginalLineOverlapCoaction318.sections,
    Adjunction.homEquiv_naturality_left, first_transpose, second_transpose] using h
end AffineSplitDiagonalTranspose318
