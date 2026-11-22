module

public import SelectedActualSameOrdinaryRootComplexLinear318
public import SelectedActualMarkedComplexCoefficientTower318
import all SelectedActualSameOrdinaryRootComplexLinear318
import all SelectedActualMarkedComplexCoefficientTower318

public section
noncomputable section

open Polynomial
open scoped Polynomial TensorProduct
open SelectedActualOriginalOrdinaryRootBaseComparison318
open SelectedActualSameOrdinaryRootComplexLinear318
open SelectedActualMarkedComplexCoefficientTower318

namespace SelectedActualSameMarkedComplexCenter318

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])
variable (L : Type) [Field L] [Algebra ℚ L] [Algebra L ℂ] [IsScalarTower ℚ L ℂ]

/-- The character on the installed entire complex monic chart is
the scalar extension of the already selected arithmetic character.
The inverse comparison, not a new root choice, determines it. -/
def complexCenter (χ : AdjoinRoot (pQ M p) →ₐ[ℚ] L) :
    AdjoinRoot (pC M p) →ₐ[ℂ] ℂ :=
  (evaluateComplexDirect ℚ L ℂ (AdjoinRoot (pQ M p)) χ).comp
    (compareOrdinaryRootAlg M p).symm.toAlgHom

/-- The equality holds on every old section, not only on the
distinguished marked x. This ensures no hidden change of character. -/
theorem complexCenter_all_old (χ : AdjoinRoot (pQ M p) →ₐ[ℚ] L)
    (a : AdjoinRoot (pQ M p)) :
    complexCenter M p L χ (compareOrdinaryRoot M p ((1 : ℂ) ⊗ₜ[ℚ] a)) =
      algebraMap L ℂ (χ a) := by
  unfold complexCenter
  change evaluateComplexDirect ℚ L ℂ (AdjoinRoot (pQ M p)) χ
    ((compareOrdinaryRootAlg M p).symm
      ((compareOrdinaryRootAlg M p) ((1 : ℂ) ⊗ₜ[ℚ] a))) = _
  rw [AlgEquiv.symm_apply_apply]
  let B := AdjoinRoot (pQ M p)
  let b : ℂ ⊗[L] (L ⊗[ℚ] B) := (1 : ℂ) ⊗ₜ[L] ((1 : L) ⊗ₜ[ℚ] a)
  have hb : chartTower ℚ L ℂ B b = (1 : ℂ) ⊗ₜ[ℚ] a := by
    change chartTower ℚ L ℂ B ((1 : ℂ) ⊗ₜ[L] ((1 : L) ⊗ₜ[ℚ] a)) =
      (1 : ℂ) ⊗ₜ[ℚ] a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]
  have h := DFunLike.congr_fun (evaluation_through_actual_tower ℚ L ℂ B χ) b
  change evaluateComplexDirect ℚ L ℂ B χ (chartTower ℚ L ℂ B b) =
    evaluateComplexTower ℚ L ℂ B χ b at h
  exact (congrArg (evaluateComplexDirect ℚ L ℂ B χ) hb).symm.trans
    (h.trans (evaluation_original_section ℚ L ℂ B χ a))

theorem center_retains_original_abscissa (χ : AdjoinRoot (pQ M p) →ₐ[ℚ] L) :
    complexCenter M p L χ (AdjoinRoot.root (pC M p)) =
      algebraMap L ℂ (χ (AdjoinRoot.root (pQ M p))) := by
  rw [← compareOrdinaryRoot_x M p]
  exact complexCenter_all_old M p L χ (AdjoinRoot.root (pQ M p))

theorem center_retains_literal_J_one (χ : AdjoinRoot (pQ M p) →ₐ[ℚ] L)
    (h : χ (AdjoinRoot.of (pQ M p) SelectedOriginalRationalOrdinary318.jCoord) = 1) :
    complexCenter M p L χ (AdjoinRoot.of (pC M p) SelectedComplexOrdinaryBase318.jCoord) = 1 := by
  rw [← compareOrdinaryRoot_j M p, complexCenter_all_old, h, map_one]

end SelectedActualSameMarkedComplexCenter318

#print axioms SelectedActualSameMarkedComplexCenter318.complexCenter_all_old
#print axioms SelectedActualSameMarkedComplexCenter318.center_retains_original_abscissa
#print axioms SelectedActualSameMarkedComplexCenter318.center_retains_literal_J_one
