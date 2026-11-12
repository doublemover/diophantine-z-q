module
public import ActualOriginalSmoothGlobalBounds318
public section
noncomputable section
namespace ActualOriginalScaledLineVariation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalCompactCircleCount318 ActualOriginalLineCorrelation318
open ActualOriginalPairedWeightVariation318 ActualOriginalFiniteAbel318
open scoped BigOperators

lemma actual_linePoint_succ (y v : Coordinates ℤ) (j : ℕ) :
    linePoint y v (j+1)=linePoint y v j+v := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    dsimp [linePoint] <;> push_cast <;> ring

/-- The literal scaled ambient weight along an original integer line. -/
@[expose] def scaledLineWeight (B : ℝ) (W : Coordinates ℝ → ℝ)
    (y v : Coordinates ℤ) (j : ℕ) : ℂ := latticeWeight B W (linePoint y v j)

lemma actual_scaled_line_amplitude (B : ℝ) (W : Coordinates ℝ → ℝ)
    (A : ℝ) (ha : ∀ x, ‖W x‖≤A) (y v : Coordinates ℤ) (j : ℕ) :
    ‖scaledLineWeight B W y v j‖≤A := by
  simpa only [scaledLineWeight,latticeWeight,Complex.norm_real] using
    ha (B⁻¹ • integerEmbed (linePoint y v j))

/-- A single lattice step costs precisely inverse scale, uniformly in
all base points. The original product-space norm and direction are retained. -/
lemma actual_scaled_line_increment (B : ℝ) (hB : 0<B) (W : Coordinates ℝ → ℝ)
    (L : ℝ) (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖)
    (y v : Coordinates ℤ) (j : ℕ) :
    ‖scaledLineWeight B W y v j-scaledLineWeight B W y v (j+1)‖≤
      (L/B)*‖integerEmbed v‖ := by
  have hh := hl (B⁻¹ • integerEmbed (linePoint y v j))
    (B⁻¹ • integerEmbed (linePoint y v (j+1)))
  have hd : B⁻¹ • integerEmbed (linePoint y v j)-
      B⁻¹ • integerEmbed (linePoint y v (j+1))= -(B⁻¹ • integerEmbed v) := by
    rw [actual_linePoint_succ,integerEmbed_add,smul_add]
    abel
  rw [hd,norm_neg,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hB] at hh
  have he : L*(B⁻¹*‖integerEmbed v‖)=(L/B)*‖integerEmbed v‖ := by ring
  rw [he] at hh
  simpa only [scaledLineWeight,latticeWeight,←Complex.ofReal_sub,Complex.norm_real] using hh

/-- The complete discrete variation is scale-uniform on every interval
whose step count is at most R*B. No translation-dependent constant. -/
theorem actual_scaled_line_variation (B : ℝ) (hB : 0<B) (W : Coordinates ℝ → ℝ)
    (L : ℝ) (hL : 0≤L) (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖)
    (R : ℝ) (y v : Coordinates ℤ) (N : ℕ) (hN : (N : ℝ)≤R*B) :
    incrementVariation (scaledLineWeight B W y v) N≤R*L*‖integerEmbed v‖ := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, (L/B)*‖integerEmbed v‖ :=
      Finset.sum_le_sum (fun j _ => actual_scaled_line_increment B hB W L hl y v j)
    _ = (N : ℝ)*((L/B)*‖integerEmbed v‖) := by simp
    _ ≤ (R*B)*((L/B)*‖integerEmbed v‖) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by field_simp [hB.ne']; ring

end ActualOriginalScaledLineVariation318
