module
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Tactic
public section
noncomputable section
namespace HolomorphicRectanglePrimitive318
open Complex Set MeasureTheory Metric Filter
open scoped Topology Interval
set_option maxHeartbeats 2400000

@[expose] def openRectangle (a b c d : ℝ) : Set ℂ := Ioo a b ×ℂ Ioo c d

theorem openRectangle_open (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem between_Ioo {a b x y t : ℝ} (hx : x∈Ioo a b) (hy : y∈Ioo a b)
    (ht : t∈[[x,y]]) : t∈Ioo a b :=
  ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) ht.1,
    lt_of_le_of_lt ht.2 (max_lt hx.2 hy.2)⟩

theorem rectangle_inside {a b c d : ℝ} {z w : ℂ}
    (hz : z∈openRectangle a b c d) (hw : w∈openRectangle a b c d) :
    Rectangle z w⊆openRectangle a b c d := by
  intro v hv
  exact ⟨between_Ioo hz.1 hw.1 hv.1,between_Ioo hz.2 hw.2 hv.2⟩

theorem horizontal_integrable (f : ℂ → ℂ) {a b c d : ℝ}
    (hc : ContinuousOn f (openRectangle a b c d)) (x y v : ℝ)
    (hx : x∈Ioo a b) (hy : y∈Ioo a b) (hv : v∈Ioo c d) :
    IntervalIntegrable (fun t : ℝ => f ((t:ℂ)+v*I)) volume x y := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp (by fun_prop)
  intro t ht
  change (((t:ℂ)+v*I).re∈Ioo a b) ∧ (((t:ℂ)+v*I).im∈Ioo c d)
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add] using And.intro (between_Ioo hx hy ht) hv

theorem vertical_integrable (f : ℂ → ℂ) {a b c d : ℝ}
    (hc : ContinuousOn f (openRectangle a b c d)) (u x y : ℝ)
    (hu : u∈Ioo a b) (hx : x∈Ioo c d) (hy : y∈Ioo c d) :
    IntervalIntegrable (fun t : ℝ => f ((u:ℂ)+t*I)) volume x y := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp (by fun_prop)
  intro t ht
  change (((u:ℂ)+t*I).re∈Ioo a b) ∧ (((u:ℂ)+t*I).im∈Ioo c d)
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add] using And.intro hu (between_Ioo hx hy ht)

/-- Path independence for the actual two-segment integrals in a rectangle.
All adjacent integrals are justified by continuity on that rectangle. -/
theorem wedge_difference (f : ℂ → ℂ) {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (p z w : ℂ) (hp : p∈openRectangle a b c d)
    (hz : z∈openRectangle a b c d) (hw : w∈openRectangle a b c d) :
    wedgeIntegral p w f-wedgeIntegral p z f=wedgeIntegral z w f := by
  have hH := intervalIntegral.integral_add_adjacent_intervals
    (horizontal_integrable f hf.continuousOn p.re z.re p.im hp.1 hz.1 hp.2)
    (horizontal_integrable f hf.continuousOn z.re w.re p.im hz.1 hw.1 hp.2)
  have hV := intervalIntegral.integral_add_adjacent_intervals
    (vertical_integrable f hf.continuousOn w.re p.im z.im hw.1 hp.2 hz.2)
    (vertical_integrable f hf.continuousOn w.re z.im w.im hw.1 hz.2 hw.2)
  let q : ℂ := z.re+p.im*I
  let r : ℂ := w.re+z.im*I
  have hq : q∈openRectangle a b c d := by
    simpa only [q,openRectangle,mem_reProdIm,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one,zero_add] using And.intro hz.1 hp.2
  have hr : r∈openRectangle a b c d := by
    simpa only [r,openRectangle,mem_reProdIm,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one,zero_add] using And.intro hw.1 hz.2
  have hR := hf.isConservativeOn q r (rectangle_inside hq hr)
  rw [←add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq] at hR
  simp only [q,r,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add,smul_eq_mul] at hR
  simp only [wedgeIntegral,smul_eq_mul]
  rw [←hH,←hV]
  linear_combination hR

/-- A genuine global primitive on every open rectangle, constructed by
integration. Local differentiation uses the pinned disk primitive theorem;
the global path-independence identity supplies the exact local join. -/
theorem primitive_derivative (f : ℂ → ℂ) {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (p : ℂ) (hp : p∈openRectangle a b c d) :
    ∀z∈openRectangle a b c d,HasDerivAt (fun w => wedgeIntegral p w f) (f z) z := by
  intro z hz
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (openRectangle_open a b c d) z hz
  have hfball := hf.mono hball
  have hlocal : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
    hfball.isConservativeOn.hasDerivAt_wedgeIntegral hfball.continuousOn (mem_ball_self hr)
  apply (hlocal.add_const (wedgeIntegral p z f)).congr_of_eventuallyEq
  filter_upwards [(openRectangle_open a b c d).mem_nhds hz] with w hw
  have h := wedge_difference f hf p z w hp hz hw
  linear_combination h

theorem actual_rectangle_primitive (f : ℂ → ℂ) {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hne : (openRectangle a b c d).Nonempty) : Complex.IsExactOn f (openRectangle a b c d) := by
  obtain ⟨p,hp⟩ := hne
  exact ⟨fun w => wedgeIntegral p w f,primitive_derivative f hf p hp⟩
end HolomorphicRectanglePrimitive318
