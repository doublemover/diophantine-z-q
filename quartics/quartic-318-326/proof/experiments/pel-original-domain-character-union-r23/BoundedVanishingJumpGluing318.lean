module
public import ActualBoundedPrimitiveTraces318
public import SchwarzReflectionReal318
public section
noncomputable section
namespace BoundedVanishingJumpGluing318
open Set Metric Filter
open scoped Topology ComplexConjugate
open HolomorphicRectanglePrimitive318 ActualBoundedPrimitiveTraces318
open SchwarzReflectionReal318
set_option maxHeartbeats 2800000

/-- The original real seam is in the closure of each actual open side,
proved by approaching through that side. -/
theorem seam_mem_closures {a b r x:ℝ} (hr:0<r) (hx:x∈Ioo a b) :
    (x:ℂ)∈closure (openRectangle a b 0 r) ∧
    (x:ℂ)∈closure (openRectangle a b (-r) 0) := by
  have ht : ∀ᶠt in 𝓝[>] (0:ℝ),t<r := nhdsWithin_le_nhds (eventually_lt_nhds hr)
  constructor
  · apply mem_closure_of_tendsto (upper_path_limit x)
    filter_upwards [self_mem_nhdsWithin,ht] with t hp hlt
    exact upper_path_mem hx hp hlt
  · apply mem_closure_of_tendsto (lower_path_limit x)
    filter_upwards [self_mem_nhdsWithin,ht] with t hp hlt
    exact lower_path_mem hx hp hlt

theorem closed_upper_subset {a b r:ℝ} (hr:0<r) :
    openRectangle a b (-r) r∩upperClosed⊆closure (openRectangle a b 0 r) := by
  intro z hz
  have hz0:0≤z.im := hz.2
  rcases eq_or_lt_of_le hz0 with heq|hpos
  · have he:z=(z.re:ℂ) := by apply Complex.ext <;> simp [heq.symm]
    rw [he]
    exact (seam_mem_closures hr hz.1.1).1
  · exact subset_closure ⟨hz.1.1,⟨hpos,hz.1.2.2⟩⟩

theorem closed_lower_subset {a b r:ℝ} (hr:0<r) :
    openRectangle a b (-r) r∩lowerClosed⊆closure (openRectangle a b (-r) 0) := by
  intro z hz
  have hz0:z.im≤0 := hz.2
  rcases lt_or_eq_of_le hz0 with hneg|heq
  · exact subset_closure ⟨hz.1.1,⟨hz.1.2.1,hneg⟩⟩
  · have he:z=(z.re:ℂ) := by apply Complex.ext <;> simp [heq]
    rw [he]
    exact (seam_mem_closures hr hz.1.1).2

@[expose] def joinedPrimitive (g₊ g₋:ℂ→ℂ) (c:ℂ) (z:ℂ) : ℂ :=
  if 0≤z.im then g₊ z else g₋ z+c

theorem joined_continuous (g₊ g₋:ℂ→ℂ) (c:ℂ) {a b r:ℝ} (hr:0<r)
    (hc₊:ContinuousOn g₊ (closure (openRectangle a b 0 r)))
    (hc₋:ContinuousOn g₋ (closure (openRectangle a b (-r) 0)))
    (hmatch:∀x∈Ioo a b,g₊ (x:ℂ)=g₋ (x:ℂ)+c) :
    ContinuousOn (joinedPrimitive g₊ g₋ c) (openRectangle a b (-r) r) := by
  unfold joinedPrimitive
  apply ContinuousOn.if
  · intro z hz
    have hz0 := frontier_upper_im_zero z hz.2
    have he:z=(z.re:ℂ) := by apply Complex.ext <;> simp [hz0]
    simpa only [←he] using hmatch z.re hz.1.1
  · simpa only [upperClosed_closed.closure_eq] using hc₊.mono (closed_upper_subset hr)
  · apply ((hc₋.mono (closed_lower_subset hr)).add continuousOn_const).mono
    intro z hz
    exact ⟨hz.1,closure_upper_compl_subset hz.2⟩

theorem joined_upper_derivative (f₊ g₊ g₋:ℂ→ℂ) (c:ℂ) {a b r:ℝ}
    (hd₊:∀z∈openRectangle a b 0 r,HasDerivAt g₊ (f₊ z) z)
    {z:ℂ} (hz:z∈openRectangle a b 0 r) :
    HasDerivAt (joinedPrimitive g₊ g₋ c) (f₊ z) z := by
  apply (hd₊ z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.2.1] with w hw
  simp only [joinedPrimitive,if_pos hw.le]

theorem joined_lower_derivative (f₋ g₊ g₋:ℂ→ℂ) (c:ℂ) {a b r:ℝ}
    (hd₋:∀z∈openRectangle a b (-r) 0,HasDerivAt g₋ (f₋ z) z)
    {z:ℂ} (hz:z∈openRectangle a b (-r) 0) :
    HasDerivAt (joinedPrimitive g₊ g₋ c) (f₋ z) z := by
  apply ((hd₋ z hz).add_const c).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz.2.2] with w hw
  simp only [joinedPrimitive,if_neg (not_le.mpr hw)]

/-- Genuine analytic gluing from a bounded vanishing jump, WITHOUT
assuming either function has a complex boundary value. Actual bounded
primitives are constructed and extended to the closure; their traces
are matched by uniform mean value; Morera glues the primitive; taking
its derivative gives the requested holomorphic extension of both
ORIGINAL functions. -/
theorem bounded_vanishing_jump_gluing (f₊ f₋:ℂ→ℂ) {a b r:ℝ}
    (hab:a<b) (hr:0<r)
    (hf₊:DifferentiableOn ℂ f₊ (openRectangle a b 0 r))
    (hf₋:DifferentiableOn ℂ f₋ (openRectangle a b (-r) 0))
    (C₊ C₋:ℝ≥0)
    (hC₊:∀z∈openRectangle a b 0 r,‖f₊ z‖₊≤C₊)
    (hC₋:∀z∈openRectangle a b (-r) 0,‖f₋ z‖₊≤C₋)
    (hjump:∀x∈Ioo a b,Tendsto (fun z=>f₊ z-f₋ (conj z))
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 0)) :
    ∃F:ℂ→ℂ,DifferentiableOn ℂ F (openRectangle a b (-r) r) ∧
      (∀z∈openRectangle a b 0 r,F z=f₊ z) ∧
      (∀z∈openRectangle a b (-r) 0,F z=f₋ z) := by
  obtain ⟨g₊,g₋,c,hc₊,hc₋,hd₊,hd₋,hmatch⟩ :=
    bounded_pair_matching_primitives f₊ f₋ hab hr hf₊ hf₋ C₊ C₋ hC₊ hC₋ hjump
  let G := joinedPrimitive g₊ g₋ c
  have hG:DifferentiableOn ℂ G (openRectangle a b (-r) r) := by
    apply HolomorphicGluingAcrossReal318.differentiableOn_of_continuousOn_off_real
      G _ (openRectangle_open a b (-r) r) (joined_continuous g₊ g₋ c hr hc₊ hc₋ hmatch)
    intro z hz hne
    rcases lt_or_gt_of_ne hne with hneg|hpos
    · exact (joined_lower_derivative f₋ g₊ g₋ c hd₋ ⟨hz.1,⟨hz.2.1,hneg⟩⟩).differentiableAt
    · exact (joined_upper_derivative f₊ g₊ g₋ c hd₊ ⟨hz.1,⟨hpos,hz.2.2⟩⟩).differentiableAt
  refine ⟨deriv G,hG.deriv (openRectangle_open a b (-r) r),?_,?_⟩
  · intro z hz
    exact (joined_upper_derivative f₊ g₊ g₋ c hd₊ hz).deriv
  · intro z hz
    exact (joined_lower_derivative f₋ g₊ g₋ c hd₋ hz).deriv
end BoundedVanishingJumpGluing318
