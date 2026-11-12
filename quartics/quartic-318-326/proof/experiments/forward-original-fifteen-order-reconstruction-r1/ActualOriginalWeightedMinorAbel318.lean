module
public import ActualOriginalFiveQuadraticPrefixes318
public section
noncomputable section
namespace ActualOriginalWeightedMinorAbel318
open QuadricCRTAssembly318 ActualOriginalJointPrefixControl318 ActualOriginalFiveQuadraticPrefixes318
open ActualOriginalSmoothIntegratedAbel318 ActualOriginalCanonicalSupportBox318
open ActualOriginalFiniteCircleIdentity318 ActualOriginalFiniteBoxProduct318 ActualOriginalBoxOverlap318
open ActualOriginalFiveAxisCancellation318 ActualOriginalIntervalSliceIdentity318
open ActualOriginalUniformMixedPlaneVariation318 ActualOriginalIntegerTiling318
open ActualOriginalCompactCircleCount318 ActualOriginalMajorArcDomain318 MeasureTheory
open scoped BigOperators ContDiff

@[expose] def lowerCorner (H : ℕ) : Coordinates ℤ :=
  ((-(H : ℤ),-(H : ℤ)),(-(H : ℤ),-(H : ℤ)),-(H : ℤ))

/-- Only the quadratic PHASE is split into five characters. The SAME
arbitrary g stays evaluated at the complete original five-coordinate point. -/
lemma actual_original_weighted_time_rectangle (κ : ℤ) (H : ℕ) (g : Coordinates ℤ → ℂ) (t : ℝ) :
    timeRectangle g (quadraticFiveAxes κ H) (lowerCorner H) t=
      originalCircleSum κ (centeredBox H) g (t : AddCircle (1 : ℝ)) := by
  have hlen : ((H : ℤ)-(-(H : ℤ))+1).toNat=2*H+1 := by omega
  have hp (x : Coordinates ℤ) : fourier (equation κ x) (t : AddCircle (1 : ℝ))=
      fourier (x.1.1^2) (t : AddCircle (1 : ℝ))*fourier (x.1.2^2) (t : AddCircle (1 : ℝ))*
      fourier (-x.2.1.1^2) (t : AddCircle (1 : ℝ))*fourier (-x.2.1.2^2) (t : AddCircle (1 : ℝ))*
      fourier ((-κ)*x.2.2^2) (t : AddCircle (1 : ℝ)) := by
    simp only [←fourier_add]
    congr 1
    dsimp [equation]
    ring
  simp only [originalCircleSum,Finset.sum_apply,centeredBox,originalBox,Finset.sum_product]
  simp_rw [actual_integer_interval_sum]
  simp only [hlen,hp]
  simp [timeRectangle,quadraticFiveAxes,quadraticTimeAxis,lowerCorner,firstDirection,
    secondDirection,thirdDirection,fourthDirection,fifthDirection,nsmul_eq_mul,
    Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]

/-- Actual NONSEPARABLE smooth weighted original box minor integral.
The constant is produced before B,H,N. Every mixed Abel boundary term
is controlled, using four moments and one produced minor supremum rather
than five pointwise factors or an invalid maximal-prefix moment. -/
theorem actual_weighted_original_box_minor (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ N H : ℕ, 0<N → ∀ B R δ : ℝ,
      0<B → ((N : ℝ)+1)^3≤B → 0≤R → 2*(H : ℝ)≤R*B → 0<δ →
      (∫ t in minorDomain N B,
        ‖originalCircleSum κ (centeredBox H) (latticeWeight B W) (t : AddCircle (1 : ℝ))‖)≤
        C*(1+R)^5*originalPrefixIntegralBudget κ H N B δ := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_integrated_abel W hW hc
  refine ⟨C,hC,fun N H hN B R δ hB hs hR hsize hδ => ?_⟩
  have ha : ∀ a∈quadraticFiveAxes κ H,
      ‖integerEmbed a.step‖≤1 ∧ (a.steps : ℝ)≤R*B := by
    intro a ha
    simp only [quadraticFiveAxes,List.mem_cons,List.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;>
      simp [quadraticTimeAxis,integerEmbed,firstDirection,secondDirection,thirdDirection,
        fourthDirection,fifthDirection,Prod.norm_def,hsize]
  have hh := hb B R (originalPrefixIntegralBudget κ H N B δ) hB hR
    (actual_prefix_integral_budget_nonneg κ H N B δ hδ)
    (volume.restrict (minorDomain N B)) (quadraticFiveAxes κ H) (by simp [quadraticFiveAxes]) ha
    (fun _ => 1) (actual_original_joint_prefix_control κ hκ N H hN B hB hs δ hδ) (lowerCorner H)
  simpa only [one_mul,actual_original_weighted_time_rectangle,quadraticFiveAxes,List.length_cons,
    List.length_nil] using hh.2

end ActualOriginalWeightedMinorAbel318
