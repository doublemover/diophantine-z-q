module
public import ActualOriginalScaledAllDifferenceOrders318
public section
noncomputable section
namespace ActualOriginalFiveOrderWeightControl318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalIteratedDifference318 ActualOriginalScaledPairedMixedDifference318
open ActualOriginalScaledAllDifferenceOrders318
open scoped ContDiff BigOperators

/-- ONE produced constant controls orders0 through5 simultaneously.
All corners,boundaries and full five-fold differences therefore use the
same weight-dependent constant, chosen before B,h or lattice directions. -/
theorem actual_uniform_five_order_weight_control (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 0<B → ∀ h : Coordinates ℤ,
      ∀ us : List (Coordinates ℤ), us.length≤5 → ∀ x,
      ‖mixedDifference (latticePairedWeight B W h) us x‖≤
        (C/B^us.length)*directionProduct (us.map integerEmbed) := by
  classical
  choose C hC hb using fun k : Fin 6 => actual_scaled_paired_all_orders W hW hc k.val
  refine ⟨∑ k : Fin 6, C k,Finset.sum_nonneg (fun k hk => hC k),fun B hB h us hu x => ?_⟩
  let k : Fin 6 := ⟨us.length,by omega⟩
  have hk : C k≤∑ j : Fin 6, C j :=
    Finset.single_le_sum (fun j hj => hC j) (Finset.mem_univ k)
  apply (hb k B hB h us rfl x).trans
  apply mul_le_mul_of_nonneg_right
  · simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hk (inv_nonneg.mpr (pow_nonneg (le_of_lt hB) _))
  · exact actual_direction_product_nonneg (fun u => norm_nonneg u) (us.map integerEmbed)

lemma actual_direction_product_le_one {E : Type*} [NormedAddCommGroup E]
    (us : List E) (hu : ∀ u∈us, ‖u‖≤1) : directionProduct us≤1 := by
  revert hu
  induction us with
  | nil => intro hu; exact le_rfl
  | cons u us ih =>
    intro hu
    have hhead := hu u (List.mem_cons_self)
    have htail := ih (fun v hv => hu v (List.mem_cons_of_mem u hv))
    exact (mul_le_mul hhead htail
      (actual_direction_product_nonneg (fun v => norm_nonneg v) us) zero_le_one).trans_eq (one_mul 1)

/-- In particular all original unit-coordinate directions and all their
subsets/repetitions up to order5 have the exact B^-order cost. -/
theorem actual_unit_direction_five_order_weight_control (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 0<B → ∀ h : Coordinates ℤ,
      ∀ us : List (Coordinates ℤ), us.length≤5 →
      (∀ u∈us, ‖integerEmbed u‖≤1) → ∀ x,
      ‖mixedDifference (latticePairedWeight B W h) us x‖≤C/B^us.length := by
  obtain ⟨C,hC,hb⟩ := actual_uniform_five_order_weight_control W hW hc
  refine ⟨C,hC,fun B hB h us hu hunit x => ?_⟩
  apply (hb B hB h us hu x).trans
  have hp : directionProduct (us.map integerEmbed)≤1 := by
    apply actual_direction_product_le_one
    intro u hu'
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu'
    exact hunit v hv
  exact (mul_le_mul_of_nonneg_left hp (div_nonneg hC (pow_nonneg (le_of_lt hB) _))).trans_eq (mul_one _)

end ActualOriginalFiveOrderWeightControl318
