module
public import PELOriginalCM210NativeSignature318
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Analysis.Real.Pi.Bounds
public section
noncomputable section
namespace PELOriginalCM210MinkowskiBound318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeDiscriminant318
open PELOriginalCM210NativeSignature318 NumberField.InfinitePlace
@[expose] def bound : ℝ := (4/Real.pi)^nrComplexPlaces K*
  (((Module.finrank ℚ K).factorial:ℝ)/(Module.finrank ℚ K:ℝ)^(Module.finrank ℚ K)*
    Real.sqrt |(NumberField.discr K:ℝ)|)
lemma bound_eq : bound=2*Real.sqrt 840/Real.pi := by
  norm_num [bound,complex_places,degree_two,native_discriminant] <;> ring
lemma bound_lt_nineteen : bound<19 := by
  rw [bound_eq]
  apply (div_lt_iff₀ Real.pi_pos).mpr
  have hs : Real.sqrt 840<29 := by
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤840)
    have hnonneg := Real.sqrt_nonneg (840:ℝ)
    nlinarith
  have hp := Real.pi_gt_d2
  nlinarith

end PELOriginalCM210MinkowskiBound318
