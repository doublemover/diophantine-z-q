module
public import ContactTrueGlobalTensorPullback318
public import OriginalWholeIntrinsicSections318
public section
noncomputable section
namespace OriginalTrueGlobalZoomComparison318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
  (i : Fin 4)

/-- The arithmetic model candidate's section equals the pullback of the
GENUINE global intrinsic bicanonical q0 on the actual proper Q-normalization.
Both sides are full differential tensors on the same genuine generic chart. -/
theorem global0 :
    OriginalWholeIntrinsicSections318.differentialImage c t w D I
      (OriginalWholeIntrinsicSections318.global0 c t w D) =
    ContactTrueGlobalTensorPullback318.image c i
      (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i)
      (ContactGlobalBicanonical318.q0 c) := by
  rw [ContactTrueGlobalTensorPullback318.image_q0]
  exact OriginalWholeIntrinsicSections318.global0_original c t w D I i

/-- Same global q1, same whole branch map, same Q-to-K differential base
change. No equality of formal coefficients substitutes for global restriction. -/
theorem global1 :
    OriginalWholeIntrinsicSections318.differentialImage c t w D I
      (OriginalWholeIntrinsicSections318.global1 c t w D) =
    ContactTrueGlobalTensorPullback318.image c i
      (OriginalAllPrimeIntegralBicanonical318.originalBranchMap c t w D I i)
      (ContactGlobalBicanonical318.q1 c) := by
  rw [ContactTrueGlobalTensorPullback318.image_q1]
  exact OriginalWholeIntrinsicSections318.global1_original c t w D I i
end OriginalTrueGlobalZoomComparison318
