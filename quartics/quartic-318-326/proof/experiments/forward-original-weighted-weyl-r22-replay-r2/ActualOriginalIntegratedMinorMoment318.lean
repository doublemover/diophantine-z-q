module
public import ActualOriginalWeightedMinorAbel318
public section
noncomputable section
namespace ActualOriginalIntegratedMinorMoment318
open QuadricCRTAssembly318 ActualOriginalWeightedMinorAbel318 ActualOriginalFiveQuadraticPrefixes318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalCompactCircleCount318 ActualOriginalScaledCircle318
open ActualOriginalMajorArcDomain318 ActualOriginalCircleMinorArcIdentity318 MeasureTheory
open scoped ContDiff

@[expose] def canonicalMomentRadius (R B : ℝ) : ℕ := (⌈R*B⌉ : ℤ).toNat

/-- The literal full original smooth minor-arc integral now has the
four-moment/one-supremum bound, with W-dependent constants produced before
all scales. This is quantitative but is NOT yet an asymptotic o(B^3)
theorem: compatible choices of N, B and the divisor exponent remain. -/
theorem actual_original_integrated_minor_moment (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ N : ℕ, 0<N → ∀ B δ : ℝ,
      1≤B → ((N : ℝ)+1)^3≤B → 0<δ →
      ‖minorArcIntegral κ N B W‖≤
        C*(2*R+3)^5*originalPrefixIntegralBudget κ (canonicalMomentRadius R B) N B δ := by
  obtain ⟨R,hR,hr⟩ := actual_compact_canonical_support W hc
  obtain ⟨C,hC,hb⟩ := actual_weighted_original_box_minor κ hκ W hW hc
  refine ⟨R,C,hR,hC,fun N hN B δ hB hs hδ => ?_⟩
  have hBp : 0<B := by linarith
  have hH := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have heH : (canonicalMomentRadius R B : ℤ)=⌈R*B⌉ := Int.toNat_of_nonneg hH
  have heR : (canonicalMomentRadius R B : ℝ)=(⌈R*B⌉ : ℝ) := by exact_mod_cast heH
  have hsize : 2*(canonicalMomentRadius R B : ℝ)≤(2*R+2)*B := by
    rw [heR]
    have hh := Int.ceil_lt_add_one (R*B)
    nlinarith
  have hsupport : ∀ z∉centeredBox (canonicalMomentRadius R B), latticeWeight B W z=0 := by
    rw [heH]
    exact hr B hBp
  have hbound := hb N (canonicalMomentRadius R B) hN B (2*R+2) δ hBp hs
    (by linarith) hsize hδ
  calc
    _ ≤ ∫ t in minorDomain N B, ‖scaledCircleSum κ t B W‖ := norm_integral_le_integral_norm _
    _ = ∫ t in minorDomain N B,
        ‖ActualOriginalFiniteCircleIdentity318.originalCircleSum κ
          (centeredBox (canonicalMomentRadius R B)) (latticeWeight B W) (t : AddCircle (1 : ℝ))‖ := by
      simp_rw [actual_circle_eq_finite κ B W _ hsupport]
    _ ≤ _ := by convert hbound using 1 <;> ring

end ActualOriginalIntegratedMinorMoment318
