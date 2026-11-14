module
public import ActualOriginalIntegratedMultiaxisAbel318
public section
noncomputable section
namespace ActualOriginalUnpairedMixedWeight318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalIteratedDifference318 ActualOriginalSmoothAllDifferenceOrders318
open ActualOriginalScaledAllDifferenceOrders318 ActualOriginalFiveOrderWeightControl318
open scoped ContDiff BigOperators

/-- The original UNPAIRED weight W(x/B), not W(x/B)W((x+h)/B).
The smooth compact all-order producer is applied directly to W. -/
theorem actual_unpaired_scaled_order (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 0<B → ∀ us : List (Coordinates ℤ),
      us.length=k → ∀ x,
      ‖mixedDifference (latticeWeight B W) us x‖≤
        C*(B⁻¹)^k*directionProduct (us.map integerEmbed) := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_all_difference_orders (Coordinates ℝ) k ℝ W hW hc
  refine ⟨C,hC,fun B hB us hu x => ?_⟩
  have he : mixedDifference (latticeWeight B W) us x=
      (mixedDifference W (us.map (fun u => B⁻¹ • integerEmbed u))
        (B⁻¹ • integerEmbed x) : ℂ) := by
    change mixedDifference (fun z => (W (B⁻¹ • integerEmbed z) : ℂ)) us x=_
    rw [actual_mixed_ofReal,actual_mixed_comp_additive]
    exact fun z u => by rw [integerEmbed_add,smul_add]
  rw [he,Complex.norm_real]
  have hh := hb (us.map (fun u => B⁻¹ • integerEmbed u))
    (by simpa only [List.length_map] using hu) (B⁻¹ • integerEmbed x)
  rw [actual_scaled_direction_product B hB,hu] at hh
  simpa only [mul_assoc] using hh

/-- One W-dependent constant is produced before scales, translations,
rectangles and phases, for all mixed orders zero through five. -/
theorem actual_unpaired_five_order_control (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 0<B → ∀ us : List (Coordinates ℤ),
      us.length≤5 → (∀ u∈us, ‖integerEmbed u‖≤1) → ∀ x,
      ‖mixedDifference (latticeWeight B W) us x‖≤C*(B⁻¹)^us.length := by
  classical
  choose C hC hb using fun k : Fin 6 => actual_unpaired_scaled_order W hW hc k.val
  refine ⟨∑ k : Fin 6, C k,Finset.sum_nonneg (fun k hk => hC k),fun B hB us hu had x => ?_⟩
  let k : Fin 6 := ⟨us.length,by omega⟩
  have hk : C k≤∑ j : Fin 6, C j :=
    Finset.single_le_sum (fun j hj => hC j) (Finset.mem_univ k)
  have hp : directionProduct (us.map integerEmbed)≤1 := by
    apply actual_direction_product_le_one
    intro u hu'
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu'
    exact had v hv
  apply (hb k B hB us rfl x).trans
  calc
    _ ≤ C k*(B⁻¹)^us.length*1 := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (hC k) (pow_nonneg (inv_nonneg.mpr (le_of_lt hB)) _))
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg (inv_nonneg.mpr (le_of_lt hB)) _)

end ActualOriginalUnpairedMixedWeight318
