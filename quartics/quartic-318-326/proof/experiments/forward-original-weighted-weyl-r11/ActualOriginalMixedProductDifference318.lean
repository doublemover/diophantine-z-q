module
public import ActualOriginalSmoothMixedDifference318
public section
noncomputable section
namespace ActualOriginalMixedProductDifference318

lemma actual_norm_four_terms (a b c d : ℝ) :
    ‖a+b+c+d‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
  calc
    _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
    _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ _ := add_le_add_right (add_le_add_right (norm_add_le _ _) _) _

/-- Exact product mixed-difference identity: BOTH mixed differences and
BOTH cross-products of first differences occur. -/
lemma actual_mixed_product_identity (u₀₀ u₁₀ u₀₁ u₁₁ v₀₀ v₁₀ v₀₁ v₁₁ : ℝ) :
    (u₀₀*v₀₀-u₁₀*v₁₀)-(u₀₁*v₀₁-u₁₁*v₁₁)=
      ((u₀₀-u₁₀)-(u₀₁-u₁₁))*v₀₀+
      (u₁₀-u₁₁)*(v₀₀-v₁₀)+(u₀₁-u₁₁)*(v₀₀-v₀₁)+
      u₁₁*((v₀₀-v₁₀)-(v₀₁-v₁₁)) := by ring

/-- Generic four-corner product bound used for the actual translated
weight and the actual unshifted weight, with no separability hypothesis. -/
theorem actual_mixed_product_bound (u₀₀ u₁₀ u₀₁ u₁₁ v₀₀ v₁₀ v₀₁ v₁₁ : ℝ)
    (A B U₀ U₁ V₀ V₁ DU DV : ℝ)
    (ha : ‖u₁₁‖≤A) (hb : ‖v₀₀‖≤B)
    (hu₀ : ‖u₀₁-u₁₁‖≤U₀) (hu₁ : ‖u₁₀-u₁₁‖≤U₁)
    (hv₀ : ‖v₀₀-v₁₀‖≤V₀) (hv₁ : ‖v₀₀-v₀₁‖≤V₁)
    (hdu : ‖(u₀₀-u₁₀)-(u₀₁-u₁₁)‖≤DU)
    (hdv : ‖(v₀₀-v₁₀)-(v₀₁-v₁₁)‖≤DV) :
    ‖(u₀₀*v₀₀-u₁₀*v₁₀)-(u₀₁*v₀₁-u₁₁*v₁₁)‖≤DU*B+U₁*V₀+U₀*V₁+A*DV := by
  rw [actual_mixed_product_identity]
  apply (actual_norm_four_terms _ _ _ _).trans
  simp only [norm_mul]
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul hdu hb (norm_nonneg _) ((norm_nonneg _).trans hdu)
      · exact mul_le_mul hu₁ hv₀ (norm_nonneg _) ((norm_nonneg _).trans hu₁)
    · exact mul_le_mul hu₀ hv₁ (norm_nonneg _) ((norm_nonneg _).trans hu₀)
  · exact mul_le_mul ha hdv (norm_nonneg _) ((norm_nonneg _).trans ha)

end ActualOriginalMixedProductDifference318
