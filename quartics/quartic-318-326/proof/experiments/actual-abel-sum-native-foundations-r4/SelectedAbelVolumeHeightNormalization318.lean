module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Ring
public section
noncomputable section

open NumberField
open scoped BigOperators Classical

namespace SelectedAbelVolumeHeightNormalization318

/-- No period matrix: the actual oriented volume is read with the
Gaudron--Rémond normalization π^(-g) of the squared wedge norm. -/
def normalizedArchLog (g : ℕ) (vol : ℂ) : ℝ :=
  -Real.log (Real.sqrt (‖vol‖ / Real.pi^g))

theorem normalizedArchLog_eq (g : ℕ) (vol : ℂ) (hv : vol ≠ 0) :
    normalizedArchLog g vol = -Real.log (Real.sqrt ‖vol‖) +
      (g : ℝ) * (Real.log Real.pi / 2) := by
  unfold normalizedArchLog
  have hd : ‖vol‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hπ : Real.pi ^ g ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  rw [Real.log_sqrt (div_nonneg (norm_nonneg _) (pow_nonneg Real.pi_pos.le _)),
    Real.log_div hd hπ,Real.log_pow,Real.log_sqrt (norm_nonneg _)]
  ring

variable (L : Type) [Field L] [NumberField L]

/-- One average over all embeddings of the actual volume, once and
in the same common field used by the finite determinant lattice. -/
def archVolumeDegree (g : ℕ) (vol : (L →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  (∑ s : L →ₐ[ℚ] ℂ, normalizedArchLog g (vol s)) /
    (Module.finrank ℚ L : ℝ)

theorem archVolumeDegree_eq (g : ℕ) (vol : (L →ₐ[ℚ] ℂ) → ℂ)
    (nz : ∀ s, vol s ≠ 0) :
    archVolumeDegree L g vol =
      (∑ s : L →ₐ[ℚ] ℂ, -Real.log (Real.sqrt ‖vol s‖)) /
        (Module.finrank ℚ L : ℝ) + (g : ℝ) * (Real.log Real.pi / 2) := by
  have hn : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := L)).ne'
  have hcard : Fintype.card (L →ₐ[ℚ] ℂ) = Module.finrank ℚ L := AlgHom.card ℚ L ℂ
  unfold archVolumeDegree
  simp_rw [fun s => normalizedArchLog_eq g (vol s) (nz s)]
  rw [Finset.sum_add_distrib,add_div,Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
  congr 1
  exact (div_eq_iff hn).2 (mul_comm _ _)

end SelectedAbelVolumeHeightNormalization318

#print axioms SelectedAbelVolumeHeightNormalization318.archVolumeDegree_eq
