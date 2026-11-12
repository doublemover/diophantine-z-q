module
public import ActualOriginalFinitePrimitiveRayCover318
public section
noncomputable section
namespace ActualOriginalFinitePrimitiveMass318
open QuadricCRTAssembly318 ActualOriginalPrimitiveRegionRays318 ActualOriginalFinitePrimitiveRayCover318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalCompactCircleCount318 ActualOriginalRealGoodRegion318 ActualOriginalSmoothGlobalBounds318
open scoped BigOperators

/-- Finitely many primitive rays have only a linear weighted mass in
the true support radius. The original sum and original weight are kept. -/
lemma actual_finite_ray_weighted_mass {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (S : Finset (Quadric κ)) (hS : ∀ u∈goodPrimitivePoints κ γ,u∈S)
    (W : Coordinates ℝ → ℝ) (hW : ∀ y∈tsupport W,y∈region γ)
    (B : ℝ) (hB : 0<B) (H : ℕ)
    (hsupport : ∀ z∉centeredBox (H : ℤ), latticeWeight B W z=0)
    (M : ℝ) (hM : 0≤M) (hm : ∀ z, ‖latticeWeight B W z‖≤M) :
    ‖compactZeroCount κ B W‖≤(S.card : ℝ)*((H : ℝ)+1)*M := by
  classical
  have hz (z : Coordinates ℤ) (hnot : z∉rayBox κ S H) :
      (if equation κ z=0 then latticeWeight B W z else 0)=0 := by
    split_ifs with he
    · by_contra hn
      exact hnot (actual_primitive_ray_support κ γ S hS W hW B hB H hsupport z he hn)
    · rfl
  unfold compactZeroCount
  rw [tsum_eq_sum (s := rayBox κ S H) hz]
  calc
    _ ≤ ∑ z∈rayBox κ S H, ‖if equation κ z=0 then latticeWeight B W z else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _z∈rayBox κ S H, M := by
      apply Finset.sum_le_sum
      intro z hz
      split_ifs
      · exact hm z
      · simpa only [norm_zero] using hM
    _ = ((rayBox κ S H).card : ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hh : ((rayBox κ S H).card : ℝ)≤(S.card : ℝ)*((H : ℝ)+1) := by
        exact_mod_cast actual_ray_box_card κ S H
      exact mul_le_mul_of_nonneg_right hh hM

/-- A finite global primitive set would force O(B), with its cardinality
and the actual compact weight amplitude retained in the constant. -/
theorem actual_finite_primitive_linear_mass {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (hfinite : (goodPrimitivePoints κ γ).Finite)
    (W : Coordinates ℝ → ℝ) (hW : Continuous W) (hc : HasCompactSupport W)
    (hregion : ∀ y∈tsupport W,y∈region γ) :
    ∃ A : ℝ, 0≤A ∧ ∀ B : ℝ, 1≤B → ‖compactZeroCount κ B W‖≤A*B := by
  classical
  let S := hfinite.toFinset
  have hS : ∀ u∈goodPrimitivePoints κ γ,u∈S := by
    intro u hu
    exact hfinite.mem_toFinset.mpr hu
  obtain ⟨R,hR,hr⟩ := actual_compact_canonical_support W hc
  obtain ⟨M,hM,hm⟩ := actual_compact_global_bound W hW hc
  let A := (S.card : ℝ)*M*(R+2)
  have hA : 0≤A := mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hM) (by linarith)
  refine ⟨A,hA,fun B hB => ?_⟩
  have hBp : 0<B := by linarith
  let H := canonicalMomentRadius R B
  have hHi := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have heH : (H : ℤ)=⌈R*B⌉ := Int.toNat_of_nonneg hHi
  have heR : (H : ℝ)=(⌈R*B⌉ : ℝ) := by exact_mod_cast heH
  have hlen : (H : ℝ)+1≤(R+2)*B := by
    rw [heR]
    have hh := Int.ceil_lt_add_one (R*B)
    nlinarith
  have hs : ∀ z∉centeredBox (H : ℤ), latticeWeight B W z=0 := by
    rw [heH]
    exact hr B hBp
  have hmass := actual_finite_ray_weighted_mass κ γ S hS W hregion B hBp H hs M hM
    (fun z => by simpa only [latticeWeight,Complex.norm_real] using hm (B⁻¹ • ActualOriginalIntegerTiling318.integerEmbed z))
  apply hmass.trans
  have hh := mul_le_mul_of_nonneg_left hlen (show 0≤(S.card : ℝ)*M by positivity)
  dsimp [A]
  nlinarith only [hh]

end ActualOriginalFinitePrimitiveMass318
