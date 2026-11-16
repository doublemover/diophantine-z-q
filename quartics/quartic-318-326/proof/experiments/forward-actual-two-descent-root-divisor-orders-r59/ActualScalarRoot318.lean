module
public import ThreeDetectorCRTWitness318
public section
noncomputable section
namespace ActualScalarRoot318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 CompressedOrientation318
open CompressedAnchorWitness318 (shiftWitness)
open GeneratorScalarProgression318 (normCoefficient)
set_option maxHeartbeats 0

/-- Original minus-translation branch, using the already fixed compression
orientation at the second labelled point. -/
@[expose] def root (n : ℤ) : K := -(1/(chartU n*shiftWitness (chartU n) (chartV n)))
@[expose] def inverseNorm (n : ℤ) : ℚ := (normCoefficient (root n))⁻¹

lemma root_ne (n : ℤ) (h0 : n≠0) (h1 : n≠1) : root n≠0 := by
  have hu : chartU n≠0 := fun he => h0 ((chartU_zero_iff n).mp he)
  exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero hu
    (CompressedChartDomains318.shift_chart_ne n h0 h1)))

/-- The literal scalar Jacobi equation follows from the actual reciprocal
compression equation after inversion; no full source witness is assumed. -/
lemma kummer (n : ℤ) (h0 : n≠0) (h1 : n≠1) :
    (fixedRoot n*root n)^2-k^2*(root n)^2-2*m*fixedRoot n*root n-
      k^2*(fixedRoot n)^2-D=0 := by
  have hu : chartU n≠0 := fun he => h0 ((chartU_zero_iff n).mp he)
  have hs := CompressedChartDomains318.shift_chart_ne n h0 h1
  have he := CompressedAnchorWitness318.compression_equation (chartU n) (chartV n) hu (chart_curve n)
  unfold fixedRoot root
  field_simp [hu,hs]
  linear_combination he

lemma scalar_curve_identity (n : ℤ) (h0 : n≠0) (h1 : n≠1) :
    (k^2*fixedRoot n-root n*(fixedRoot n*root n-m))^2=
      k^2*((root n)^4-D) := by
  have he := kummer n h0 h1
  have hp := CompressedPoint318.constant_equation
  linear_combination ((root n)^2-k^2)*he+(root n)^2*hp

lemma root_abs_gt_one (σ : K →+* ℝ) (n : ℤ) (h0 : n≠0) (h1 : n≠1) :
    1< |σ (root n)| := by
  have he := congrArg σ (scalar_curve_identity n h0 h1)
  simp only [map_pow,map_mul,map_sub] at he
  have hd : 1 < σ CompressedOrientation318.D := by
    simpa only [CoherentMultipleCharts318.D_eq] using RealMultiples318.real_D_gt_one σ
  have hk : σ k≠0 := fun hz => CompressedPoint318.k_ne (σ.injective (by simpa using hz))
  by_contra! hsmall
  have hs : (σ (root n))^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hsmall
  have h4 : (σ (root n))^4≤1 := by nlinarith [sq_nonneg (σ (root n)),sq_nonneg ((σ (root n))^2-1)]
  have hneg : (σ k)^2*((σ (root n))^4-σ D)<0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hk) (by linarith)
  rw [←he] at hneg
  exact (not_lt_of_ge (sq_nonneg _)) hneg

lemma norm_abs_gt_one (n : ℤ) (h0 : n≠0) (h1 : n≠1) :
    1< |normCoefficient (root n)| := by
  have hp := root_abs_gt_one ActualQuadraticEmbeddings318.positiveEmbedding n h0 h1
  have hm := root_abs_gt_one ActualQuadraticEmbeddings318.negativeEmbedding n h0 h1
  have he := GeneratorScalarProgression318.embedding_product (root n)
  have hprod : 1< |ActualQuadraticEmbeddings318.positiveEmbedding (root n)*
      ActualQuadraticEmbeddings318.negativeEmbedding (root n)| := by
    rw [abs_mul]
    nlinarith
  rw [he] at hprod
  exact_mod_cast hprod

lemma norm_ne (n : ℤ) (h0 : n≠0) (h1 : n≠1) : normCoefficient (root n)≠0 := by
  have hb := norm_abs_gt_one n h0 h1
  exact abs_pos.mp (by linarith)

lemma inverseNorm_bound (n : ℤ) (h0 : n≠0) (h1 : n≠1) : |inverseNorm n|<1 := by
  have hp := norm_abs_gt_one n h0 h1
  unfold inverseNorm
  rw [abs_inv]
  exact (inv_lt_one₀ (by linarith : 0< |normCoefficient (root n)|)).mpr hp

end ActualScalarRoot318
