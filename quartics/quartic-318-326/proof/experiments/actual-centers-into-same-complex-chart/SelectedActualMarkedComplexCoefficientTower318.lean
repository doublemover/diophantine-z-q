module

public import Mathlib.RingTheory.TensorProduct.Maps

public section

noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace SelectedActualMarkedComplexCoefficientTower318

variable (k L C B : Type*) [CommRing k] [CommRing L] [CommRing C] [CommRing B]
  [Algebra k L] [Algebra k C] [Algebra k B] [Algebra L C] [IsScalarTower k L C]

/-- Extend the actual arithmetic chart along its given embedding of
the common field; the arithmetic and complex tensors are compared
without choosing a new root. -/
abbrev chartTower : C ⊗[L] (L ⊗[k] B) ≃ₐ[C] C ⊗[k] B :=
  Algebra.TensorProduct.cancelBaseChange k L C C B

/-- Evaluation from a chosen character on the original chart.
The extended character is determined by the actual scalar map. -/
def evaluate (χ : B →ₐ[k] L) : L ⊗[k] B →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) χ (fun _ _ => mul_comm _ _)

def evaluateComplexDirect (χ : B →ₐ[k] L) : C ⊗[k] B →ₐ[C] C :=
  Algebra.TensorProduct.lift (AlgHom.id C C) ((IsScalarTower.toAlgHom k L C).comp χ)
    (fun _ _ => mul_comm _ _)

def evaluateComplexTower (χ : B →ₐ[k] L) : C ⊗[L] (L ⊗[k] B) →ₐ[C] C :=
  Algebra.TensorProduct.lift (AlgHom.id C C)
    ((Algebra.ofId L C).comp (evaluate k L B χ)) (fun _ _ => mul_comm _ _)

/-- The chart character commutes with the full scalar tower as an
algebra map, not just on its independently chosen root. -/
theorem evaluation_through_actual_tower (χ : B →ₐ[k] L) :
    (evaluateComplexDirect k L C B χ).comp (chartTower k L C B).toAlgHom =
      evaluateComplexTower k L C B χ := by
  let E := (evaluateComplexDirect k L C B χ).comp (chartTower k L C B).toAlgHom
  let F := evaluateComplexTower k L C B χ
  apply AlgHom.ext
  intro x
  change E x = F x
  refine TensorProduct.induction_on x (by rw [map_zero,map_zero]) ?_ ?_
  · intro c y
    refine TensorProduct.induction_on y (by rw [TensorProduct.tmul_zero,map_zero,map_zero]) ?_ ?_
    · intro ℓ b
      unfold E F evaluateComplexDirect evaluateComplexTower evaluate
      simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, chartTower,
        Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.lift_tmul,
        AlgHom.id_apply, IsScalarTower.coe_toAlgHom', Algebra.ofId_apply, Algebra.smul_def, map_mul] <;>
        ac_rfl
    · intro x y hx hy
      rw [TensorProduct.tmul_add,map_add,map_add,hx,hy]
  · intro x y hx hy
    rw [map_add,map_add,hx,hy]

/-- In particular, the two actual marked evaluations agree on the
old abscissa; no rechoice after restriction of scalars is needed. -/
theorem evaluation_original_section (χ : B →ₐ[k] L) (u : B) :
    evaluateComplexTower k L C B χ ((1 : C) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] u)) =
      algebraMap L C (χ u) := by
  unfold evaluateComplexTower evaluate
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
    Algebra.ofId_apply, one_mul]

theorem evaluation_original_center (χ : B →ₐ[k] L) (j : B) (hj : χ j = 1) :
    evaluateComplexTower k L C B χ ((1 : C) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] j)) = 1 := by
  rw [evaluation_original_section, hj, map_one]

end SelectedActualMarkedComplexCoefficientTower318

#print axioms SelectedActualMarkedComplexCoefficientTower318.evaluation_through_actual_tower
#print axioms SelectedActualMarkedComplexCoefficientTower318.evaluation_original_center
