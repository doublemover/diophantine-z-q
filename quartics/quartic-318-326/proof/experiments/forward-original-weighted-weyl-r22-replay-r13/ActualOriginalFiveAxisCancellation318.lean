module
public import ActualOriginalLinearRectangle318
public section
noncomputable section
namespace ActualOriginalFiveAxisCancellation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalAxisRectangle318 ActualOriginalSmoothAxisRectangle318
open ActualOriginalLinearRectangle318 ActualOriginalScaledPairedMixedDifference318
open ActualOriginalQuadraticPolarization318 ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalWeightedBlockReciprocalBudget318
open ActualOriginalIntervalSliceIdentity318 ActualOriginalUniformMixedPlaneVariation318
open scoped ContDiff BigOperators

/-- Full original linearized oscillatory rectangles, up to five axes,
consume the produced smooth mixed constants and every phase prefix cap. -/
theorem actual_smooth_original_axis_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B R : ℝ, 0<B → 0≤R → ∀ h : Coordinates ℤ,
      ∀ as : List (Coordinates ℤ × ℕ), as.length≤5 →
      (∀ a∈as, ‖integerEmbed a.1‖≤1 ∧ (a.2 : ℝ)≤R*B) → ∀ t : ℝ, ∀ x,
      ‖originalLinearRectangle κ (latticePairedWeight B W h) (t : AddCircle (1 : ℝ)) h as x‖≤
        C*(1+R)^as.length*axisCapProduct (as.map (originalFourierAxis κ h t)) := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_axis_rectangle W hW hc
  refine ⟨C,hC,fun B R hB hR h as hlen ha t x => ?_⟩
  rw [actual_original_linear_rectangle_factor,norm_mul]
  have hu : ‖fourier (2*originalBilinear κ h x) (t : AddCircle (1 : ℝ))‖=1 := Circle.norm_coe _
  rw [hu,one_mul]
  have hh := hb B R hB hR h (as.map (originalFourierAxis κ h t))
    (by simpa only [List.length_map] using hlen) (by
      intro a hamem
      obtain ⟨a',ha',rfl⟩ := List.mem_map.mp hamem
      exact ⟨actual_chord_cap_nonneg _ _ _ (by positivity),(ha a' ha').1,
        (ha a' ha').2,actual_original_fourier_axis_prefix κ h t a'⟩) x
  simpa only [List.length_map] using hh

@[expose] def thirdDirection : Coordinates ℤ := ((0,0),(1,0),0)
@[expose] def fourthDirection : Coordinates ℤ := ((0,0),(0,1),0)
@[expose] def fifthDirection : Coordinates ℤ := ((0,0),(0,0),1)
@[expose] def fiveAxes (N₀ N₁ N₂ N₃ N₄ : ℕ) : List (Coordinates ℤ × ℕ) :=
  [(firstDirection,N₀),(secondDirection,N₁),(thirdDirection,N₂),(fourthDirection,N₃),(fifthDirection,N₄)]
@[expose] def fivePoint (lo : Coordinates ℤ) (j₀ j₁ j₂ j₃ j₄ : ℕ) : Coordinates ℤ :=
  ((lo.1.1+(j₀ : ℤ),lo.1.2+(j₁ : ℤ)),
    (lo.2.1.1+(j₂ : ℤ),lo.2.1.2+(j₃ : ℤ)),lo.2.2+(j₄ : ℤ))

/-- Exact fivefold sum at the original coordinates, not a newly chosen
separable weight or surrogate oscillatory sum. -/
lemma actual_original_five_rectangle_identity (κ : ℤ) (g : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h lo : Coordinates ℤ) (N₀ N₁ N₂ N₃ N₄ : ℕ) :
    originalLinearRectangle κ g θ h (fiveAxes N₀ N₁ N₂ N₃ N₄) lo=
      ∑ j₀∈Finset.range (N₀+1), ∑ j₁∈Finset.range (N₁+1),
      ∑ j₂∈Finset.range (N₂+1), ∑ j₃∈Finset.range (N₃+1), ∑ j₄∈Finset.range (N₄+1),
        g (fivePoint lo j₀ j₁ j₂ j₃ j₄)*
          fourier (2*originalBilinear κ h (fivePoint lo j₀ j₁ j₂ j₃ j₄)) θ := by
  simp [originalLinearRectangle,fiveAxes,fivePoint,firstDirection,secondDirection,
    thirdDirection,fourthDirection,fifthDirection,nsmul_eq_mul]

/-- ALL FIVE actual frequencies cancel multiplicatively with produced
weight constants. The negative unit coefficients and -kappa direction
are displayed exactly; resonant caps retain their full interval length. -/
theorem actual_smooth_five_axis_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B R : ℝ, 0<B → 0≤R → ∀ h lo : Coordinates ℤ,
      ∀ N₀ N₁ N₂ N₃ N₄ : ℕ,
      (N₀ : ℝ)≤R*B → (N₁ : ℝ)≤R*B → (N₂ : ℝ)≤R*B →
      (N₃ : ℝ)≤R*B → (N₄ : ℝ)≤R*B → ∀ t : ℝ,
      ‖originalLinearRectangle κ (latticePairedWeight B W h) (t : AddCircle (1 : ℝ)) h
        (fiveAxes N₀ N₁ N₂ N₃ N₄) lo‖≤C*(1+R)^5*
          (fourierChordCap ((N₀ : ℝ)+1) (2*h.1.1) t*
          fourierChordCap ((N₁ : ℝ)+1) (2*h.1.2) t*
          fourierChordCap ((N₂ : ℝ)+1) (2*(-h.2.1.1)) t*
          fourierChordCap ((N₃ : ℝ)+1) (2*(-h.2.1.2)) t*
          fourierChordCap ((N₄ : ℝ)+1) (2*(-(κ*h.2.2))) t) := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_original_axis_cancellation κ W hW hc
  refine ⟨C,hC,fun B R hB hR h lo N₀ N₁ N₂ N₃ N₄ h₀ h₁ h₂ h₃ h₄ t => ?_⟩
  have haxis : ∀ a∈fiveAxes N₀ N₁ N₂ N₃ N₄,
      ‖integerEmbed a.1‖≤1 ∧ (a.2 : ℝ)≤R*B := by
    intro a ha
    simp only [fiveAxes,List.mem_cons,List.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;>
      simp [integerEmbed,firstDirection,secondDirection,thirdDirection,
        fourthDirection,fifthDirection,Prod.norm_def,h₀,h₁,h₂,h₃,h₄]
  have hh := hb B R hB hR h (fiveAxes N₀ N₁ N₂ N₃ N₄) (by simp [fiveAxes]) haxis t lo
  convert hh using 1 <;>
    simp [fiveAxes,axisCapProduct,originalFourierAxis,originalBilinear,
      firstDirection,secondDirection,thirdDirection,fourthDirection,fifthDirection] <;> ring

end ActualOriginalFiveAxisCancellation318
