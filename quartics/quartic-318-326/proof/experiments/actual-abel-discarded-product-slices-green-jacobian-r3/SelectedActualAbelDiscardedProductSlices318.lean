module

public import SelectedActualAbelExceptionalSetNull318
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace SelectedActualAbelDiscardedProductSlices318

open SelectedActualAbelExceptionalSetNull318

variable {ι : Type*} [Fintype ι]

/-- Every finite list of forbidden coordinate values has zero mass in the
actual ordered product chart. This is the genuine projection of an
ordered product, not an assertion about the symmetric quotient. -/
theorem ordered_discarded_source_null
    (μ : Measure ℂ) [SigmaFinite μ] [NullSingletonClass μ]
    (Q : ι → Set ℂ) (hQ : ∀ i, (Q i).Finite) :
    (Measure.pi (fun _ : ι => μ)) (⋃ i, (fun x : ι → ℂ => x i) ⁻¹' Q i) = 0 := by
  have h (i : ι) :
      (Measure.pi (fun _ : ι => μ)) ((fun x : ι → ℂ => x i) ⁻¹' Q i) = 0 :=
    Measure.pi_eval_preimage_null (fun _ : ι => μ) ((hQ i).measure_zero μ)
  exact measure_iUnion_null h

/-- The map of the forbidden ordered slices itself has zero measure on
the actual target chart, using the same baseline Haar normalization
as in the local derivative and change-of-variables calculations. -/
theorem ordered_discarded_target_null
    (μ : Measure ℂ) [SigmaFinite μ] [NullSingletonClass μ]
    [IsAddHaarMeasure (Measure.pi (fun _ : ι => μ))]
    (Q : ι → Set ℂ) (hQ : ∀ i, (Q i).Finite)
    (a : (ι → ℂ) → (ι → ℂ)) (D : (ι → ℂ) → (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hderiv : ∀ x ∈ (⋃ i, (fun y : ι → ℂ => y i) ⁻¹' Q i),
      HasFDerivWithinAt a (D x) (⋃ i, (fun y : ι → ℂ => y i) ⁻¹' Q i) x) :
    (Measure.pi (fun _ : ι => μ)) (a '' (⋃ i, (fun x : ι → ℂ => x i) ⁻¹' Q i)) = 0 :=
  discarded_image_null (Measure.pi (fun _ : ι => μ)) a D _ hderiv
    (ordered_discarded_source_null μ Q hQ)

end SelectedActualAbelDiscardedProductSlices318

#print axioms SelectedActualAbelDiscardedProductSlices318.ordered_discarded_target_null
