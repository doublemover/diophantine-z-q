module
public import ActualOriginalScaledPairedMixedDifference318
public section
noncomputable section
namespace ActualOriginalUniformMixedPlaneVariation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalIntervalSliceIdentity318 ActualOriginalTwoAxisSliceIdentity318
open ActualOriginalScaledPairedMixedDifference318 ActualOriginalMixedVariationBudget318
open ActualOriginalMixedAbelIdentity318
open scoped ContDiff

@[expose] def secondDirection : Coordinates ℤ := ((0,1),(0,0),0)
lemma actual_first_direction_norm : ‖integerEmbed firstDirection‖=1 := by
  simp [integerEmbed,firstDirection,Prod.norm_def]
lemma actual_second_direction_norm : ‖integerEmbed secondDirection‖=1 := by
  simp [integerEmbed,secondDirection,Prod.norm_def]
lemma actual_plane_first_step (lo₀ lo₁ c d e : ℤ) (i j : ℕ) :
    planePoint lo₀ lo₁ c d e (i+1) j=planePoint lo₀ lo₁ c d e i j+firstDirection := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    dsimp [planePoint,firstDirection] <;> push_cast <;> ring
lemma actual_plane_second_step (lo₀ lo₁ c d e : ℤ) (i j : ℕ) :
    planePoint lo₀ lo₁ c d e i (j+1)=planePoint lo₀ lo₁ c d e i j+secondDirection := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    dsimp [planePoint,secondDirection] <;> push_cast <;> ring

/-- The literal mixed variation in the actual two-axis cancellation
consumer now has PRODUCED scale-uniform constants. Every interior mixed
increment, both boundaries and the terminal corner are controlled. -/
theorem actual_smooth_uniform_mixed_plane_variation (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧
      ∀ B : ℝ, 0<B → ∀ R : ℝ, 0≤R → ∀ h : Coordinates ℤ,
      ∀ lo₀ lo₁ c d e : ℤ, ∀ N M : ℕ, (N : ℝ)≤R*B → (M : ℝ)≤R*B →
      mixedVariation (planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e) N M≤
        A^2+4*R*A*L+R^2*(2*A*D+2*L^2) := by
  obtain ⟨A,L,D,hA,hL,hD,hall⟩ := actual_scaled_paired_mixed_constants W hW hc
  refine ⟨A,L,D,hA,hL,hD,fun B hB R hR h lo₀ lo₁ c d e N M hN hM => ?_⟩
  have hcorner := (hall B hB h (planePoint lo₀ lo₁ c d e N M)).1
  have hfirst (i j : ℕ) :
      ‖planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i j-
        planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e (i+1) j‖≤(2*A*L)/B := by
    simpa only [actual_plane_pair_value,actual_plane_first_step,actual_first_direction_norm,mul_one] using
      (hall B hB h (planePoint lo₀ lo₁ c d e i j)).2.1 firstDirection
  have hsecond (i j : ℕ) :
      ‖planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i j-
        planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i (j+1)‖≤(2*A*L)/B := by
    simpa only [actual_plane_pair_value,actual_plane_second_step,actual_second_direction_norm,mul_one] using
      (hall B hB h (planePoint lo₀ lo₁ c d e i j)).2.1 secondDirection
  have hmixed (i j : ℕ) :
      ‖(planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i j-
          planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i (j+1))-
        (planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e (i+1) j-
          planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e (i+1) (j+1))‖≤
            (2*A*D+2*L^2)/B^2 := by
    have hm := (hall B hB h (planePoint lo₀ lo₁ c d e i j)).2.2 firstDirection secondDirection
    simp only [actual_first_direction_norm,actual_second_direction_norm,mul_one] at hm
    simp only [actual_plane_pair_value,actual_plane_first_step,actual_plane_second_step]
    apply le_trans (le_of_eq ?_) hm
    congr 1
    ring
  have hb := actual_scaled_mixed_variation_budget
    (planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e) N M B R
    (A^2) (2*A*L) (2*A*L) (2*A*D+2*L^2) hB hR
    (by positivity) (by positivity) (by positivity) hN hM hcorner
    (fun i hi => hfirst i M) (fun j hj => hsecond N j) (fun i hi j hj => hmixed i j)
  convert hb using 1 <;> ring

end ActualOriginalUniformMixedPlaneVariation318
