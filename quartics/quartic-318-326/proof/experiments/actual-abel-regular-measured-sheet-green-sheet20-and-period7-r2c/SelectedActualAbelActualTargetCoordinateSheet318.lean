module

public import SelectedActualAbelPointwiseDerivative318
public import SelectedActualAbelTargetLatticeHaar318

public section

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace SelectedActualAbelActualTargetCoordinateSheet318

open SelectedActualAbelPointwiseDerivative318 SelectedActualAbelTargetLatticeHaar318

variable {J ι : Type*} [AddCommGroup J] [MeasurableSpace J] [Finite ι]

/-- The determinant-weighted reference measure on a literal ordinary Abel
sheet maps to the canonical lattice target measure. Neither the derivative
of the ordered sum nor a chart-to-target Haar comparison is assumed. -/
theorem degreeOne_sheet_to_same_target {g : ℕ}
    (L : Submodule ℤ (OrderedPeriodCoordinates g))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L)
    (μ : Measure (OrderedPeriodCoordinates g)) [Measure.IsAddHaarMeasure μ]
    (q : OrderedPeriodCoordinates g →+ J) (hq : Measurable q)
    (hker : ∀ v : OrderedPeriodCoordinates g, q v = 0 ↔ v ∈ L)
    (F : OrderedPeriodCoordinates g → OrderedPeriodCoordinates g) (hF : Measurable F)
    (C : OrderedPeriodCoordinates g → Matrix (Fin g) (Fin g) ℂ)
    (S U : Set (OrderedPeriodCoordinates g)) (hS : MeasurableSet S)
    (hU : MeasurableSet U) (hqi : InjOn q U) (hImageMeas : MeasurableSet (q '' U))
    (hgerm : ∀ τ ∈ S, ∃ (a : Fin g → Fin g → ℂ → ℂ) (c : OrderedPeriodCoordinates g),
      (∀ i j, HasDerivAt (a i j) (C τ i j) (τ j)) ∧
      F =ᶠ[𝓝 τ] fun x i => c i + ∑ j, a i j (x j))
    (hFi : InjOn F S) (hFU : F '' S = U) :
    Measure.map (fun x => q (F x))
      ((μ.withDensity fun τ => ENNReal.ofReal (‖(C τ).det‖ ^ 2)).restrict S)
      = (targetVolume L b μ q).restrict (q '' U) := by
  let m : Measure (OrderedPeriodCoordinates g) :=
    (μ.withDensity fun τ => ENNReal.ofReal (‖(C τ).det‖ ^ 2)).restrict S
  have hm : m.map F = μ.restrict U :=
    sheet_pushforward_of_degreeOne μ F C S U hS hgerm hFi hFU
  calc
    m.map (fun x => q (F x)) = (m.map F).map q := (Measure.map_map hq hF).symm
    _ = (μ.restrict U).map q := congrArg (Measure.map q) hm
    _ = (targetVolume L b μ q).restrict (q '' U) :=
      (targetVolume_restrict_chart L b μ q hq hker U hU hqi hImageMeas).symm

end SelectedActualAbelActualTargetCoordinateSheet318

#print axioms SelectedActualAbelActualTargetCoordinateSheet318.degreeOne_sheet_to_same_target
