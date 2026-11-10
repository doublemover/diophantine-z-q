module
public import OriginalReducedPolynomialExpansions318
public section
noncomputable section
namespace OriginalReducedCoefficientHeight318
open scoped RealInnerProductSpace
open MvPolynomial LiteralSievePolynomial318 TernaryQuadraticLineCover318
open OriginalPolynomialExpansionBounds318 OriginalReducedPolynomialExpansions318
open OriginalReducedPolynomialEquiv318 OriginalReducedPolynomialProducer318
open OriginalEuclideanLattice318
set_option maxHeartbeats 5000000

/-- Four explicit coefficient-height budgets; no unknown polynomial
support cardinality or hidden coefficient-growth constant occurs. -/
@[expose] def firstHeight (κ t : ℚ) (H : ℝ) : ℝ := |(κ:ℝ)|*H^2+2*|(t:ℝ)|
@[expose] def secondHeight (κ t : ℚ) (H : ℝ) : ℝ := |((κ*(t+2):ℚ):ℝ)|*H^2+2*H^2
@[expose] def productHeight (t : ℚ) (H : ℝ) : ℝ := ((t:ℝ)^2+H^2)^2
@[expose] def normHeight (κ t : ℚ) (H : ℝ) : ℝ :=
  (|(κ:ℝ)|*H^2+H^2+|(t:ℝ)^2+2*(t:ℝ)|)^2+(t:ℝ)^2*(2*H)^2

lemma expansion_height_bounds (κ t : ℚ) (x y w : Expansion) (H : ℝ)
    (hx : weight x≤H) (hy : weight y≤H) (hw : weight w≤H) :
    weight (firstExpansion κ t x y w)≤firstHeight κ t H ∧
    weight (secondExpansion κ t x y w)≤secondHeight κ t H ∧
    weight (productExpansion t x y)≤productHeight t H ∧
    weight (normExpansion κ t x y w)≤normHeight κ t H := by
  have hH : 0≤H := (weight_nonneg x).trans hx
  have hx2 := pow_le_pow_left₀ (weight_nonneg x) hx 2
  have hy2 := pow_le_pow_left₀ (weight_nonneg y) hy 2
  have hw2 := pow_le_pow_left₀ (weight_nonneg w) hw 2
  have hxy : weight x*weight y≤H^2 := by
    simpa only [pow_two] using mul_le_mul hx hy (weight_nonneg y) hH
  obtain ⟨e1,e2,e3,e4⟩ := original_weights κ t x y w
  refine ⟨?_,?_,?_,?_⟩
  · rw [e1,firstHeight]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)) _
  · rw [e2,secondHeight]
    have hh := mul_le_mul_of_nonneg_left hw2 (abs_nonneg (((κ*(t+2):ℚ):ℝ)))
    nlinarith only [hh,hxy]
  · rw [e3,productHeight,pow_two]
    exact mul_le_mul (add_le_add_left hx2 _) (add_le_add_left hy2 _)
      (by positivity) (by positivity)
  · rw [e4,normHeight]
    have hκ := mul_le_mul_of_nonneg_left hw2 (abs_nonneg (κ:ℝ))
    have hcore : |(κ:ℝ)|*(weight w)^2+weight x*weight y+|(t:ℝ)^2+2*(t:ℝ)|≤
        |(κ:ℝ)|*H^2+H^2+|(t:ℝ)^2+2*(t:ℝ)| := by linarith
    have hcore0 : 0≤|(κ:ℝ)|*(weight w)^2+weight x*weight y+|(t:ℝ)^2+2*(t:ℝ)| :=
      add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (mul_nonneg (weight_nonneg x) (weight_nonneg y))) (abs_nonneg _)
    have hc2 := pow_le_pow_left₀ hcore0 hcore 2
    have hsum : weight x+weight y≤2*H := by linarith
    have hs2 := pow_le_pow_left₀ (add_nonneg (weight_nonneg x) (weight_nonneg y)) hsum 2
    exact add_le_add hc2 (mul_le_mul_of_nonneg_left hs2 (sq_nonneg (t:ℝ)))

/-- Actual polynomial coefficients, AFTER all like terms are collected,
are bounded using the constructed expansion and its explicit masses. -/
theorem actual_polynomial_heights (κ t : ℚ) (u v z : Vector ℚ) (H : ℝ)
    (hrows : ∀ i : Fin 3, weight (row u v z i)≤H) (d : Fin 3 →₀ ℕ) :
    |((forward u v z (firstP κ t)).coeff d:ℝ)|≤firstHeight κ t H ∧
    |((forward u v z (secondP κ t)).coeff d:ℝ)|≤secondHeight κ t H ∧
    |((forward u v z (productD t)).coeff d:ℝ)|≤productHeight t H ∧
    |((forward u v z (normK κ t)).coeff d:ℝ)|≤normHeight κ t H := by
  obtain ⟨e1,e2,e3,e4⟩ := original_expansions κ t u v z
  obtain ⟨h1,h2,h3,h4⟩ := expansion_height_bounds κ t
    (row u v z 0) (row u v z 1) (row u v z 2) H (hrows 0) (hrows 1) (hrows 2)
  rw [←e1,←e2,←e3,←e4]
  exact ⟨(coefficient_le_weight _ d).trans h1,(coefficient_le_weight _ d).trans h2,
    (coefficient_le_weight _ d).trans h3,(coefficient_le_weight _ d).trans h4⟩

/-- All coefficients in each ACTUAL reduced linear coordinate row have
absolute sum at most6 times the third sequential minimum. -/
theorem actual_row_weights (u v w z : Vector ℤ)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (i : Fin 3) :
    weight (row (rationalVector u) (rationalVector v) (rationalVector z) i)≤6*‖embed w‖ := by
  have hcoord (a : Vector ℤ) (j : Fin 3) : |embed a j|≤‖embed a‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (embed a) j
  have hU := hcoord u i
  have hV := hcoord v i
  have hZ := hcoord z i
  have hrow : weight (row (rationalVector u) (rationalVector v) (rationalVector z) i)=
      |embed u i|+|embed v i|+|embed z i| := by
    fin_cases i <;> simp [row,weight_linear,rationalVector,embed]
  rw [hrow]
  nlinarith [norm_nonneg (embed w)]

/-- Explicit same-original-basis coefficient budgets for both coprime
pairs and K. These are polynomial coefficient bounds, not just value
bounds on an integer sample or on the source box. -/
theorem original_reduced_coefficient_heights (κ label : ℤ) (u v w z : Vector ℤ)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (d : Fin 3 →₀ ℕ) :
    |((substitution u v z (firstP (κ:ℚ) (label:ℚ))).coeff d:ℝ)|≤
      firstHeight (κ:ℚ) (label:ℚ) (6*‖embed w‖) ∧
    |((substitution u v z (secondP (κ:ℚ) (label:ℚ))).coeff d:ℝ)|≤
      secondHeight (κ:ℚ) (label:ℚ) (6*‖embed w‖) ∧
    |((substitution u v z (productD (label:ℚ))).coeff d:ℝ)|≤
      productHeight (label:ℚ) (6*‖embed w‖) ∧
    |((substitution u v z (normK (κ:ℚ) (label:ℚ))).coeff d:ℝ)|≤
      normHeight (κ:ℚ) (label:ℚ) (6*‖embed w‖) :=
  actual_polynomial_heights (κ:ℚ) (label:ℚ) (rationalVector u) (rationalVector v) (rationalVector z)
    (6*‖embed w‖) (actual_row_weights u v w z huv hvw hz) d

end OriginalReducedCoefficientHeight318
