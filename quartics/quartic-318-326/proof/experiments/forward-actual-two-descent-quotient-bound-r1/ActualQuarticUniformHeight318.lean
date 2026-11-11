module
public import ActualQuarticCoefficientHeight318
public section
noncomputable section
namespace ActualQuarticUniformHeight318
open scoped BigOperators
open TernaryQuadraticLineCover318 IntegerResidueBoxCount318
open OriginalUniformEliminantHeight318 OriginalShearBoxBudget318 OriginalOffsetEliminant318
open OriginalOffsetZeroLocus318 OriginalBoundedIntegerShear318 OriginalEuclideanLattice318
open ActualAffineQuarticEliminant318 ActualQuarticCoefficientHeight318 ActualQuarticRectangleTail318
set_option maxHeartbeats 12000000

@[expose] def pointHeight (κ t : ℤ) (L : ℝ) := 109*(coefficientHeight κ t L)^9
@[expose] def fullHeight (κ t : ℤ) (A B : ℕ) (L : ℝ) :=
  1+((2*A+1:ℕ):ℝ)*(2*B+1)*pointHeight κ t L

lemma coefficient_nonneg (κ t : ℤ) (L : ℝ) : 0≤coefficientHeight κ t L := by
  dsimp [coefficientHeight,formHeight,quarticHeight]
  positivity
lemma point_nonneg (κ t : ℤ) (L : ℝ) : 0≤pointHeight κ t L := by
  have h := coefficient_nonneg κ t L
  dsimp [pointHeight]
  positivity
lemma full_one (κ t : ℤ) (A B : ℕ) (L : ℝ) : 1≤fullHeight κ t A B L := by
  have h := point_nonneg κ t L
  dsimp [fullHeight]
  exact le_add_of_nonneg_right (by positivity)

/-- Actual true quartic eliminant height with ALL coefficients supplied
from the actual coordinate boxes, including t=-2 and every direction. -/
theorem actual_point_height (κ t : ℤ) (a d : Vector ℤ) (L : ℝ) (hL : 0≤L)
    (ha : Box a L) (hd : Box d L) : |(actualEliminant κ t a d:ℝ)|≤pointHeight κ t L := by
  obtain ⟨hA,hB,hC⟩ := form_coefficients true κ t a d L hL ha hd
  obtain ⟨h4,h3,h2,h1,h0⟩ := quartic_bounds κ t a d L hL ha hd
  have hf : formHeight κ t L≤coefficientHeight κ t L := by
    have hquartic : 0≤quarticHeight κ t L := by dsimp [quarticHeight];positivity
    dsimp [coefficientHeight]
    linarith
  have hq : quarticHeight κ t L≤coefficientHeight κ t L := by
    have hform : 0≤formHeight κ t L := by dsimp [formHeight];positivity
    dsimp [coefficientHeight]
    linarith
  exact ActualQuarticEliminantHeight318.integer_bound _ _ _ _ _ _ _ _ _
    (coefficient_nonneg κ t L) (hA.trans hf) (hB.trans hf) (hC.trans hf)
    (h4.trans hq) (h3.trans hq) (h2.trans hq) (h1.trans hq) (h0.trans hq)

/-- The finite-sum rectangle height is now bounded by an EXPLICIT
polynomial in original coefficient radius, side lengths, kappa and label.
The coarse height does not replace the anisotropic counting rectangle. -/
theorem actual_rectangle_height (κ t : ℤ) (u v w z : Vector ℤ)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (A B : ℕ) (i j : ℕ) (hi : i<5) (hj : j<5) :
    rectangleHeight κ t u v (shear (i:ℤ) (j:ℤ) u v z) A B≤
      fullHeight κ t A B (heightRadius A B ‖embed w‖) := by
  classical
  let L := heightRadius A B ‖embed w‖
  have hL : 0≤L := by dsimp [L,heightRadius];positivity
  have hbound (a : Interval A×Interval B) :
      |(actualEliminant κ t (offset u v a.1.1 a.2.1) (shear (i:ℤ) (j:ℤ) u v z):ℝ)|≤pointHeight κ t L := by
    obtain ⟨ha,hd⟩ := uniform_box u v w z huv hvw hz A B i j hi hj a.1 a.2
    exact actual_point_height κ t _ _ L hL ha hd
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hbound a)
  have he : Fintype.card (Interval A×Interval B)=(2*A+1)*(2*B+1) := by
    simp only [Fintype.card_prod,Interval,Fintype.card_coe,interval_card]
  simp only [Finset.sum_const,Finset.card_univ,he,nsmul_eq_mul,Nat.cast_mul] at hh
  exact add_le_add_left hh 1

end ActualQuarticUniformHeight318
