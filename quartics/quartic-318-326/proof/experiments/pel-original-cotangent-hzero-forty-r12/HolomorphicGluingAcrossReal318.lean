module
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Tactic
public section
noncomputable section
namespace HolomorphicGluingAcrossReal318
open Complex Set MeasureTheory Metric
open scoped Interval Topology
set_option maxHeartbeats 2400000

@[expose] def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re,f ((x:ℂ)+z.im*I))-
  (∫ x : ℝ in z.re..w.re,f ((x:ℂ)+w.im*I))+
  I*(∫ y : ℝ in z.im..w.im,f ((w.re:ℂ)+y*I))-
  I*(∫ y : ℝ in z.im..w.im,f ((z.re:ℂ)+y*I))

theorem rectangleIntegral_eq_wedges (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w=wedgeIntegral z w f+wedgeIntegral w z f := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  simp only [rectangleIntegral,smul_eq_mul]

theorem rectangle_swap (z w : ℂ) : Rectangle w z=Rectangle z w := by
  simp only [Rectangle,Set.uIcc_comm]

/-- A whole rectangle lying on one closed side of the real axis has zero
integral. Differentiability is needed only on its OPEN interior; continuity
on the real edge is retained explicitly. -/
theorem rectangle_same_side (f : ℂ → ℂ) (z w : ℂ) (U : Set ℂ)
    (hc : ContinuousOn f U) (hd : ∀x∈U,x.im≠0 → DifferentiableAt ℂ f x)
    (hrect : Rectangle z w⊆U)
    (hs : (0≤z.im ∧ 0≤w.im) ∨ (z.im≤0 ∧ w.im≤0)) :
    rectangleIntegral f z w=0 := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
    (hc.mono hrect) (by
      intro x hx
      change (min z.re w.re<x.re ∧ x.re<max z.re w.re) ∧
        (min z.im w.im<x.im ∧ x.im<max z.im w.im) at hx
      have hclosed : x∈Rectangle z w := by
        change (min z.re w.re≤x.re ∧ x.re≤max z.re w.re) ∧
          (min z.im w.im≤x.im ∧ x.im≤max z.im w.im)
        exact ⟨⟨hx.1.1.le,hx.1.2.le⟩,⟨hx.2.1.le,hx.2.2.le⟩⟩
      apply (hd x (hrect hclosed) ?_).differentiableWithinAt
      rcases hs with ⟨hz,hw⟩ | ⟨hz,hw⟩
      · have hm : 0≤min z.im w.im := le_min hz hw
        exact ne_of_gt (lt_of_le_of_lt hm hx.2.1)
      · have hm : max z.im w.im≤0 := max_le hz hw
        exact ne_of_lt (lt_of_lt_of_le hx.2.2 hm))
  simpa only [rectangleIntegral,smul_eq_mul] using hh

/-- Restrict a vertical side integral to any two intermediate heights.
The integrability is derived from continuity on the ORIGINAL rectangle. -/
theorem vertical_integrable (f : ℂ → ℂ) (z w : ℂ) (hzw : z.im≤w.im)
    (hc : ContinuousOn f (Rectangle z w)) (a b c : ℝ)
    (ha : a∈[[z.re,w.re]]) (hb : z.im≤b ∧ b≤w.im) (hc' : z.im≤c ∧ c≤w.im) :
    IntervalIntegrable (fun y : ℝ => f ((a:ℂ)+y*I)) volume b c := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp (by fun_prop)
  intro y hy
  have hy' : z.im≤y ∧ y≤w.im := by
    rcases le_total b c with h | h
    · simp only [uIcc_of_le h,mem_Icc] at hy
      exact ⟨hb.1.trans hy.1,hy.2.trans hc'.2⟩
    · simp only [uIcc_of_ge h,mem_Icc] at hy
      exact ⟨hc'.1.trans hy.1,hy.2.trans hb.2⟩
  change (((a:ℂ)+y*I).re∈[[z.re,w.re]]) ∧ (((a:ℂ)+y*I).im∈[[z.im,w.im]])
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add,uIcc_of_le hzw,mem_Icc] using And.intro ha hy'

/-- Exact additive cancellation when a rectangle is cut along the REAL
axis. This is the analytic seam input to Morera, not a numerical contour
argument. -/
theorem rectangle_split_zero (f : ℂ → ℂ) (z w : ℂ)
    (hz : z.im≤0) (hw : 0≤w.im) (hc : ContinuousOn f (Rectangle z w)) :
    rectangleIntegral f z w=
      rectangleIntegral f z (w.re:ℂ)+rectangleIntegral f (z.re:ℂ) w := by
  have hzw := hz.trans hw
  have iw0 := vertical_integrable f z w hzw hc w.re z.im 0 (by simp)
    ⟨le_rfl,hzw⟩ ⟨hz,hw⟩
  have iw1 := vertical_integrable f z w hzw hc w.re 0 w.im (by simp)
    ⟨hz,hw⟩ ⟨hzw,le_rfl⟩
  have iz0 := vertical_integrable f z w hzw hc z.re z.im 0 (by simp)
    ⟨le_rfl,hzw⟩ ⟨hz,hw⟩
  have iz1 := vertical_integrable f z w hzw hc z.re 0 w.im (by simp)
    ⟨hz,hw⟩ ⟨hzw,le_rfl⟩
  have iw := intervalIntegral.integral_add_adjacent_intervals iw0 iw1
  have iz := intervalIntegral.integral_add_adjacent_intervals iz0 iz1
  simp only [rectangleIntegral,Complex.ofReal_re,Complex.ofReal_im]
  rw [←iw,←iz]
  ring

theorem lower_rectangle_subset (z w : ℂ) (hz : z.im≤0) (hw : 0≤w.im) :
    Rectangle z (w.re:ℂ)⊆Rectangle z w := by
  intro x hx
  change x.re∈[[z.re,(w.re:ℂ).re]] ∧ x.im∈[[z.im,(w.re:ℂ).im]] at hx
  simp only [Complex.ofReal_re,Complex.ofReal_im,uIcc_of_le hz,mem_Icc] at hx
  change x.re∈[[z.re,w.re]] ∧ x.im∈[[z.im,w.im]]
  rw [uIcc_of_le (hz.trans hw)]
  exact ⟨hx.1,hx.2.1,hx.2.2.trans hw⟩

theorem upper_rectangle_subset (z w : ℂ) (hz : z.im≤0) (hw : 0≤w.im) :
    Rectangle (z.re:ℂ) w⊆Rectangle z w := by
  intro x hx
  change x.re∈[[(z.re:ℂ).re,w.re]] ∧ x.im∈[[(z.re:ℂ).im,w.im]] at hx
  simp only [Complex.ofReal_re,Complex.ofReal_im,uIcc_of_le hw,mem_Icc] at hx
  change x.re∈[[z.re,w.re]] ∧ x.im∈[[z.im,w.im]]
  rw [uIcc_of_le (hz.trans hw)]
  exact ⟨hx.1,hz.trans hx.2.1,hx.2.2⟩

theorem rectangle_zero_ordered (f : ℂ → ℂ) (z w : ℂ) (hzw : z.im≤w.im)
    (U : Set ℂ) (hc : ContinuousOn f U)
    (hd : ∀x∈U,x.im≠0 → DifferentiableAt ℂ f x) (hrect : Rectangle z w⊆U) :
    rectangleIntegral f z w=0 := by
  by_cases hz : 0≤z.im
  · exact rectangle_same_side f z w U hc hd hrect (Or.inl ⟨hz,hz.trans hzw⟩)
  by_cases hw : w.im≤0
  · exact rectangle_same_side f z w U hc hd hrect (Or.inr ⟨hzw.trans hw,hw⟩)
  have hz' : z.im≤0 := (lt_of_not_ge hz).le
  have hw' : 0≤w.im := (lt_of_not_ge hw).le
  rw [rectangle_split_zero f z w hz' hw' (hc.mono hrect)]
  have h₀ := rectangle_same_side f z (w.re:ℂ) U hc hd
    ((lower_rectangle_subset z w hz' hw').trans hrect) (Or.inr ⟨hz',by simp⟩)
  have h₁ := rectangle_same_side f (z.re:ℂ) w U hc hd
    ((upper_rectangle_subset z w hz' hw').trans hrect) (Or.inl ⟨by simp,hw'⟩)
  rw [h₀,h₁,add_zero]

/-- Continuous holomorphic functions on the two sides of a straight seam
glue holomorphically. Rectangle splitting constructs Morera's hypothesis;
no differentiability along the seam is assumed. -/
theorem differentiableOn_of_continuousOn_off_real (f : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀x∈U,x.im≠0 → DifferentiableAt ℂ f x) : DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,hc⟩
  intro z w hrect
  rw [←add_eq_zero_iff_eq_neg,←rectangleIntegral_eq_wedges]
  rcases le_total z.im w.im with h | h
  · exact rectangle_zero_ordered f z w h U hc hd hrect
  · have hh := rectangle_zero_ordered f w z h U hc hd (by rwa [rectangle_swap])
    rw [rectangleIntegral_eq_wedges] at hh ⊢
    simpa only [add_comm] using hh
end HolomorphicGluingAcrossReal318
