module
public import ActualOriginalBoundedPrimitiveCover318
public section
noncomputable section
namespace ActualOriginalBoundedPrimitiveMass318
open QuadricCRTAssembly318 ActualOriginalBoundedPrimitiveBox318 ActualOriginalBoundedPrimitiveCover318
open ActualOriginalFinitePrimitiveRayCover318 ActualOriginalPrimitiveRegionRays318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalCompactCircleCount318 ActualOriginalRealGoodRegion318 ActualOriginalSmoothGlobalBounds318
open scoped BigOperators

/-- The actual bounded primitive carrier controls the original weighted mass
with the exact radius factor. The original sum and original weight are kept. -/
lemma actual_bounded_primitive_weighted_mass {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (W : Coordinates ℝ → ℝ) (hW : ∀ y∈tsupport W,y∈region γ)
    (B : ℝ) (hB : 0<B) (H : ℕ)
    (hsupport : ∀ z∉centeredBox (H : ℤ), latticeWeight B W z=0)
    (M : ℝ) (hM : 0≤M) (hm : ∀ z, ‖latticeWeight B W z‖≤M) :
    ‖compactZeroCount κ B W‖≤((primitiveBox κ γ H).card : ℝ)*((H : ℝ)+1)*M := by
  classical
  have hz (z : Coordinates ℤ) (hnot : z∉rayBox κ (primitiveBox κ γ H) H) :
      (if equation κ z=0 then latticeWeight B W z else 0)=0 := by
    split_ifs with he
    · by_contra hn
      exact hnot (actual_bounded_primitive_cover κ γ W hW B hB H hsupport z he hn)
    · rfl
  unfold compactZeroCount
  rw [tsum_eq_sum (s := rayBox κ (primitiveBox κ γ H) H) hz]
  calc
    _ ≤ ∑ z∈rayBox κ (primitiveBox κ γ H) H, ‖if equation κ z=0 then latticeWeight B W z else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _z∈rayBox κ (primitiveBox κ γ H) H, M := by
      apply Finset.sum_le_sum
      intro z hz
      split_ifs
      · exact hm z
      · simpa only [norm_zero] using hM
    _ = ((rayBox κ (primitiveBox κ γ H) H).card : ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hh : ((rayBox κ (primitiveBox κ γ H) H).card : ℝ)≤((primitiveBox κ γ H).card : ℝ)*((H : ℝ)+1) := by
        exact_mod_cast actual_ray_box_card κ (primitiveBox κ γ H) H
      exact mul_le_mul_of_nonneg_right hh hM


/-- A fixed positive weight/support constant bounds the entire count
by B times the number of true primitive points in its canonical box. -/
theorem actual_bounded_primitive_linear_mass {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (W : Coordinates ℝ → ℝ) (hW : Continuous W) (hc : HasCompactSupport W)
    (hregion : ∀ y∈tsupport W,y∈region γ) :
    ∃ R A : ℝ, 1≤R ∧ 0<A ∧ ∀ B : ℝ, 1≤B →
      ‖compactZeroCount κ B W‖≤
        ((primitiveBox κ γ (canonicalMomentRadius R B)).card : ℝ)*A*B := by
  obtain ⟨R,hR,hr⟩ := actual_compact_canonical_support W hc
  obtain ⟨M,hM,hm⟩ := actual_compact_global_bound W hW hc
  let A := (R+2)*(M+1)
  refine ⟨R,A,hR,mul_pos (by linarith) (by linarith),fun B hB => ?_⟩
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
  have hmass := actual_bounded_primitive_weighted_mass κ γ W hregion B hBp H hs M hM
    (fun z => by simpa only [latticeWeight,Complex.norm_real] using hm (B⁻¹ • ActualOriginalIntegerTiling318.integerEmbed z))
  let C : ℝ := (primitiveBox κ γ H).card
  have hC : 0≤C := Nat.cast_nonneg _
  calc
    _ ≤ C*((H : ℝ)+1)*M := hmass
    _ ≤ C*((R+2)*B)*M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hC) hM
    _ ≤ C*((R+2)*B)*(M+1) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (mul_nonneg (by linarith) hBp.le))
    _ = _ := by dsimp [A,C,H]; ring
end ActualOriginalBoundedPrimitiveMass318
