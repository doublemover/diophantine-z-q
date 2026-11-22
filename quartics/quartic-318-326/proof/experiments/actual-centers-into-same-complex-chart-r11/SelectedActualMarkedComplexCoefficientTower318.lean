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

private theorem evaluate_tmul (χ : B →ₐ[k] L) (ℓ : L) (b : B) :
    evaluate k L B χ (ℓ ⊗ₜ[k] b) = ℓ * χ b :=
  Algebra.TensorProduct.lift_tmul (AlgHom.id L L) χ (fun _ _ => mul_comm _ _) ℓ b

private theorem evaluateComplexDirect_tmul (χ : B →ₐ[k] L) (c : C) (b : B) :
    evaluateComplexDirect k L C B χ (c ⊗ₜ[k] b) = c * algebraMap L C (χ b) :=
  Algebra.TensorProduct.lift_tmul (AlgHom.id C C) ((IsScalarTower.toAlgHom k L C).comp χ)
    (fun _ _ => mul_comm _ _) c b

private theorem evaluateComplexTower_tmul (χ : B →ₐ[k] L) (c : C) (ℓ : L) (b : B) :
    evaluateComplexTower k L C B χ (c ⊗ₜ[L] (ℓ ⊗ₜ[k] b)) =
      c * algebraMap L C (ℓ * χ b) := by
  calc
    evaluateComplexTower k L C B χ (c ⊗ₜ[L] (ℓ ⊗ₜ[k] b)) =
        (AlgHom.id C C) c * ((Algebra.ofId L C).comp (evaluate k L B χ)) (ℓ ⊗ₜ[k] b) :=
      Algebra.TensorProduct.lift_tmul (AlgHom.id C C)
        ((Algebra.ofId L C).comp (evaluate k L B χ)) (fun _ _ => mul_comm _ _) c
        (ℓ ⊗ₜ[k] b)
    _ = c * algebraMap L C (ℓ * χ b) := by
      rw [AlgHom.id_apply,AlgHom.comp_apply,Algebra.ofId_apply,evaluate_tmul]

/-- The chart character commutes with the full scalar tower as an
algebra map, not just on its independently chosen root. -/
theorem evaluation_through_actual_tower (χ : B →ₐ[k] L) :
    (evaluateComplexDirect k L C B χ).comp (chartTower k L C B).toAlgHom =
      evaluateComplexTower k L C B χ := by
  let E := (evaluateComplexDirect k L C B χ).comp (chartTower k L C B).toAlgHom
  let F := evaluateComplexTower k L C B χ
  apply Algebra.TensorProduct.ext'
  intro c y
  change E (c ⊗ₜ[L] y) = F (c ⊗ₜ[L] y)
  refine TensorProduct.inductionOn
    (motive := fun z : L ⊗[k] B => E (c ⊗ₜ[L] z) = F (c ⊗ₜ[L] z)) y ?_ ?_
  · intro ℓ b
    calc
      E (c ⊗ₜ[L] (ℓ ⊗ₜ[k] b)) = (ℓ • c) * algebraMap L C (χ b) := by
        change evaluateComplexDirect k L C B χ
          (chartTower k L C B (c ⊗ₜ[L] (ℓ ⊗ₜ[k] b))) = _
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        exact evaluateComplexDirect_tmul k L C B χ (ℓ • c) b
      _ = c * algebraMap L C (ℓ * χ b) := by
        rw [Algebra.smul_def,map_mul]
        ac_rfl
      _ = F (c ⊗ₜ[L] (ℓ ⊗ₜ[k] b)) := (evaluateComplexTower_tmul k L C B χ c ℓ b).symm
  · intro x z hx hz
    change E (c ⊗ₜ[L] (x + z)) = F (c ⊗ₜ[L] (x + z))
    rw [TensorProduct.tmul_add,map_add,map_add,hx,hz]

/-- In particular, the two actual marked evaluations agree on the
old abscissa; no rechoice after restriction of scalars is needed. -/
theorem evaluation_original_section (χ : B →ₐ[k] L) (u : B) :
    evaluateComplexTower k L C B χ ((1 : C) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] u)) =
      algebraMap L C (χ u) := by
  rw [evaluateComplexTower_tmul,one_mul,one_mul]

theorem evaluation_original_center (χ : B →ₐ[k] L) (j : B) (hj : χ j = 1) :
    evaluateComplexTower k L C B χ ((1 : C) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] j)) = 1 := by
  rw [evaluation_original_section, hj, map_one]

end SelectedActualMarkedComplexCoefficientTower318

#print axioms SelectedActualMarkedComplexCoefficientTower318.evaluation_through_actual_tower
#print axioms SelectedActualMarkedComplexCoefficientTower318.evaluation_original_center
