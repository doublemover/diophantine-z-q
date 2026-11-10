module
public import ActualThreeQParameter318
public import ThreeParameterGrowth318
public section
noncomputable section
open Filter Topology
open scoped MatrixGroups
namespace ActualThreeQMeromorphic318
open ActualThreeQParameter318 ActualThreeCuspHomeomorph318 ActualThreeCuspJ318
open WidthQParameter318
set_option maxHeartbeats 0

lemma eventually_punctured (g : SL(2,ℤ)) :
    ∀ᶠ q in 𝓝[≠] (0:ℂ), q ∈ punctured (wReal g) 2 := by
  have hr : ∀ᶠ q in 𝓝 (0:ℂ), ‖q‖ < radius (wReal g) 2 :=
    (continuous_norm.continuousAt : ContinuousAt (fun q : ℂ => ‖q‖) 0).eventually
      (isOpen_Iio.mem_nhds (by simpa using radius_positive (wReal g) 2))
  filter_upwards [hr.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hne
  exact ⟨hne,hq⟩

/-- Actual q-period parameter has polynomial growth of degree at most its
actual cusp width. The estimate uses its exact j identity and leading term. -/
theorem qParameter_bound (g : SL(2,ℤ)) :
    ∀ᶠ q in 𝓝[≠] (0:ℂ), ‖q^natWidth g * qParameter g q‖ ≤ 518 := by
  have hG : ∀ᶠ q in 𝓝 (0:ℂ), ‖ActualQJ318.G (q^natWidth g)‖ < 2 := by
    apply (leading_analytic g).continuousAt.norm.eventually (p := fun x : ℝ => x < 2)
    apply isOpen_Iio.mem_nhds
    change ‖ActualQJ318.G ((0:ℂ)^natWidth g)‖ < 2
    rw [leading_value]
    norm_num
  filter_upwards [eventually_punctured g,hG.filter_mono nhdsWithin_le_nhds] with q hq hGq
  have hqn : ‖q‖ < 1 := lt_trans hq.2 (radius_lt_one _ _ (wReal_pos g) (by norm_num))
  have hpow : ‖q‖^natWidth g ≤ 1 := pow_le_one₀ (norm_nonneg q) hqn.le
  have hj := ThreeParameterGrowth318.norm_le_j (qParameter g q) (qParameter_ne_zero g hq)
  have hprod : ‖q‖^natWidth g * ‖ThreeCompactParameter318.J (qParameter g q)‖ =
      ‖ActualQJ318.G (q^natWidth g)‖ := by
    rw [j_identity g hq, jExpression, norm_div, norm_pow]
    exact mul_div_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hq.1))
  rw [norm_mul,norm_pow]
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ ‖q‖^natWidth g by positivity)
  nlinarith

/-- The exact original global quotient coordinate is meromorphic at the origin
of every genuine filled q-disc. This supplies the missing cusp germ, rather
than postulating an extension of a rational target parameter. -/
theorem qParameter_meromorphic (g : SL(2,ℤ)) : MeromorphicAt (qParameter g) 0 := by
  apply ThreeParameterGrowth318.meromorphic_of_polynomial_bound (natWidth g) 518
  · exact (eventually_punctured g).mono fun q hq => (qParameter_analytic g q hq).differentiableAt
  · exact qParameter_bound g

end ActualThreeQMeromorphic318
