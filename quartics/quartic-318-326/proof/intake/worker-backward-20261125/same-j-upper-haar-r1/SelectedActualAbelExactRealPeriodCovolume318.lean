module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Pi

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace SelectedActualAbelExactRealPeriodCovolume318

abbrev V (g : ℕ) := Fin g → ℂ
abbrev RealRow (g : ℕ) := Σ _ : Fin g, Fin 2

/-- Consecutive real and imaginary entries, in the complex frame's
unchanged row order. No new orientation or period basis is chosen. -/
def orderedRealCoordinates (g : ℕ) : V g ≃ₗ[ℝ] (RealRow g → ℝ) :=
  (LinearEquiv.piCongrRight (fun _ : Fin g => Complex.basisOneI.equivFun)).trans
    (LinearEquiv.piCurry ℝ (fun (_ : Fin g) (_ : Fin 2) => ℝ)).symm

private def realReferenceBasis (g : ℕ) : Module.Basis (RealRow g) ℝ (V g) :=
  Module.Basis.ofEquivFun (orderedRealCoordinates g)

private theorem realReference_repr (g : ℕ) (z : V g) (i : RealRow g) :
    (realReferenceBasis g).repr z i = Complex.measurableEquivPi (z i.1) i.2 := by
  rw [realReferenceBasis, Module.Basis.ofEquivFun_repr_apply] <;> rfl

private theorem complex_unit_box_volume :
    (volume : Measure ℂ) (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  let U : Set (Fin 2 → ℝ) := Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)
  have hU : MeasurableSet U := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  have he : Complex.measurableEquivPi ⁻¹' U = ZSpan.fundamentalDomain Complex.basisOneI := by
    ext z
    rw [ZSpan.mem_fundamentalDomain]
    change (∀ i ∈ (Set.univ : Set (Fin 2)), Complex.measurableEquivPi z i ∈ Set.Ico (0 : ℝ) 1) ↔ _
    have hRep (i : Fin 2) :
        Complex.measurableEquivPi z i = Complex.basisOneI.repr z i := rfl
    simp only [hRep, Set.mem_univ, true_implies]
  have hm : (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' U) =
      (volume : Measure (Fin 2 → ℝ)) U := by
    rw [← Measure.map_apply Complex.measurableEquivPi.measurable hU,
      Complex.volume_preserving_equiv_pi.map_eq]
  rw [← he, hm]
  change (volume : Measure (Fin 2 → ℝ)) (Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) = 1
  rw [Real.volume_pi_Ico]
  simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

private theorem real_reference_box_volume (g : ℕ) :
    (volume : Measure (V g)).real (ZSpan.fundamentalDomain (realReferenceBasis g)) = 1 := by
  have he : ZSpan.fundamentalDomain (realReferenceBasis g) =
      Set.univ.pi (fun _ => ZSpan.fundamentalDomain Complex.basisOneI) := by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies,
      realReference_repr]
    have hRep (i : Fin g) (k : Fin 2) :
        Complex.measurableEquivPi (z i) k = Complex.basisOneI.repr (z i) k := rfl
    constructor
    · intro h i k
      exact (hRep i k) ▸ h ⟨i,k⟩
    · intro h i
      exact (hRep i.1 i.2).symm ▸ h i.1 i.2
  have h : (volume : Measure (V g)) (ZSpan.fundamentalDomain (realReferenceBasis g)) = 1 := by
    rw [he, MeasureTheory.volume_pi_pi]
    simp only [complex_unit_box_volume, Finset.prod_const_one]
  exact (congrArg ENNReal.toReal h).trans ENNReal.toReal_one

/-- The actual integer periods are the columns. The real/imaginary
coordinates are determined by the original complex row, and no
extra determinant, factor of π, or real volume scaling enters. -/
@[expose] def literalRealPeriodMatrix {g : ℕ} {L : Submodule ℤ (V g)}
    (b : Module.Basis (RealRow g) ℤ L) : Matrix (RealRow g) (RealRow g) ℝ :=
  fun i j => Complex.measurableEquivPi (((b j : L) : V g) i.1) i.2

/-- Entrywise reading of the same literal matrix, without changing the
period and volume normalizations. Consumers use this named equality. -/
theorem literalRealPeriodMatrix_apply {g : ℕ} {L : Submodule ℤ (V g)}
    (b : Module.Basis (RealRow g) ℤ L) (i j : RealRow g) :
    literalRealPeriodMatrix b i j = Complex.measurableEquivPi (((b j : L) : V g) i.1) i.2 :=
  rfl

theorem covolume_eq_literal_real_period_determinant {g : ℕ}
    (L : Submodule ℤ (V g)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (RealRow g) ℤ L) :
    ZLattice.covolume L (volume : Measure (V g)) = |(literalRealPeriodMatrix b).det| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b (realReferenceBasis g),
    real_reference_box_volume, mul_one, Module.Basis.det_apply]
  have h : (realReferenceBasis g).toMatrix ((↑) ∘ b) = literalRealPeriodMatrix b := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    change (realReferenceBasis g).repr ((b j : L) : V g) i =
      Complex.measurableEquivPi (((b j : L) : V g) i.1) i.2
    exact realReference_repr g ((b j : L) : V g) i
  rw [h]

end SelectedActualAbelExactRealPeriodCovolume318

#print axioms SelectedActualAbelExactRealPeriodCovolume318.covolume_eq_literal_real_period_determinant

#print axioms SelectedActualAbelExactRealPeriodCovolume318.literalRealPeriodMatrix_apply
