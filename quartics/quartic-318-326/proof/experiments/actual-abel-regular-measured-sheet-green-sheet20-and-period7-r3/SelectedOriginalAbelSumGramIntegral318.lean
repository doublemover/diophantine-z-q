module
public import SelectedGammaOneFinitePetersson318
public import SelectedConstructPeterssonFrame318
public import SelectedAbelSumGramProductIntegral318
import all SelectedConstructPeterssonFrame318
public section
noncomputable section

open MeasureTheory
open scoped BigOperators Matrix
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedGammaOneQuotientArea318
open SelectedConstructPeterssonFrame318 SelectedAbelSumGramProductIntegral318

namespace SelectedOriginalAbelSumGramIntegral318

variable {M g : ℕ} (h5 : 5 ≤ M) (f : Fin g → Form M)

/-- Integral of the expanded product density produced by the actual
ordered forms on the literal quotient. It does not pass to chosen
periods or a replacement quotient measure. -/
abbrev originalVolumeIntegral : ℂ :=
  ∫ z, ∑ s : Equiv.Perm (Fin g), ∑ t : Equiv.Perm (Fin g),
    summand (fun i j => cross (f i) (f j)) s t z
      ∂(Measure.pi (fun _ : Fin g => area M h5))

theorem original_volume_integral :
    originalVolumeIntegral h5 f = (g.factorial : ℂ) * (originalGram h5 f).det := by
  letI : IsFiniteMeasure (area M h5) := SelectedGammaOneFinitePetersson318.area_finite M h5
  exact integral_double_permutation (area M h5) (fun i j => cross (f i) (f j))
    (fun i j => SelectedGammaOneFinitePetersson318.cross_integrable M h5 (f i) (f j))

/-- The one remaining geometric equality is the change of variables
for the actual Abel sum, with its genuine sheet count. Given it, the
Jacobian volume is the literal determinant; there is no period
matrix or artificial Gram in the conclusion. -/
theorem volume_eq_gram (vol : ℂ)
    (hcover : (g.factorial : ℂ) * vol = originalVolumeIntegral h5 f) :
    vol = (originalGram h5 f).det := by
  have hn : (g.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero g)
  exact mul_left_cancel₀ hn (hcover.trans (original_volume_integral h5 f))

end SelectedOriginalAbelSumGramIntegral318

#print axioms SelectedOriginalAbelSumGramIntegral318.original_volume_integral
#print axioms SelectedOriginalAbelSumGramIntegral318.volume_eq_gram
