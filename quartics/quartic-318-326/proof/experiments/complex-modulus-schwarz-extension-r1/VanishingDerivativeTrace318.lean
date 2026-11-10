module
public import CompactBoundaryJump318
public import Mathlib.Analysis.Calculus.MeanValue
public section
noncomputable section
namespace VanishingDerivativeTrace318
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 2400000

/-- A pointwise limit of actual differentiable interval functions is
constant when their derivatives vanish UNIFORMLY on that interval.
No derivative of the limiting trace is assumed. -/
theorem limit_constant_of_uniform_derivative {T : Type*} (l : Filter T) [NeBot l]
    (F D : T → ℝ → ℂ) (trace : ℝ → ℂ) {a b : ℝ} (hab : a≤b)
    (hlim : ∀x∈Icc a b,Tendsto (fun t=>F t x) l (𝓝 (trace x)))
    (hderiv : ∀ε:ℝ,0<ε → ∀ᶠt in l,
      ∀x∈Icc a b,HasDerivWithinAt (F t) (D t x) (Icc a b) x ∧ ‖D t x‖≤ε) :
    ∀x∈Icc a b,trace x=trace a := by
  intro x hx
  have ha : a∈Icc a b := ⟨le_rfl,hab⟩
  have hnorm : ‖trace x-trace a‖≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ := ε/(‖x-a‖+1)
    have hden : 0<‖x-a‖+1 := by positivity
    have hδ : 0<δ := div_pos hε hden
    have hbound : ‖trace x-trace a‖≤δ*‖x-a‖ := by
      apply le_of_tendsto ((hlim x hx).sub (hlim a ha)).norm
      filter_upwards [hderiv δ hδ] with t ht
      exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy=>(ht y hy).1) (fun y hy=>(ht y hy).2) convex_Icc ha hx
    have hmul : δ*(‖x-a‖+1)=ε := div_mul_cancel₀ ε (ne_of_gt hden)
    have hsmall : δ*‖x-a‖≤ε := by nlinarith
    simpa only [zero_add] using hbound.trans hsmall
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

/-- The compact-collar theorem supplies the uniform derivative bound on
parallel segments. The approaching trace is constant without assuming
that the trace is differentiable, or that the derivatives extend. -/
theorem horizontal_trace_constant (jump : ℂ → ℂ) (F : ℝ → ℝ → ℂ)
    (trace : ℝ → ℂ) {a b : ℝ} (hab : a≤b)
    (hjump : ∀x∈Icc a b,
      Tendsto jump (𝓝[{z:ℂ | 0<z.im}] (x:ℂ)) (𝓝 0))
    (hlim : ∀x∈Icc a b,Tendsto (fun t=>F t x) (𝓝[>] (0:ℝ)) (𝓝 (trace x)))
    (hderiv : ∀ᶠt in 𝓝[>] (0:ℝ),∀x∈Icc a b,
      HasDerivWithinAt (F t) (jump ((x:ℂ)+Complex.I*t)) (Icc a b) x) :
    ∀x∈Icc a b,trace x=trace a := by
  apply limit_constant_of_uniform_derivative (𝓝[>] (0:ℝ)) F
    (fun t x=>jump ((x:ℂ)+Complex.I*t)) trace hab hlim
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := CompactBoundaryJump318.uniform_horizontal_jump jump a b hjump hε
  have htδ : ∀ᶠt in 𝓝[>] (0:ℝ),t<δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  filter_upwards [hderiv,self_mem_nhdsWithin,htδ] with t hd ht htδ'
  intro x hx
  exact ⟨hd x hx,(hbound t ht htδ' x hx).le⟩

/-- Applied to the DIFFERENCE of two actual primitive families, the
preceding result constructs the one additive constant that makes their
whole boundary traces agree. -/
theorem primitive_traces_differ_by_constant (jump : ℂ → ℂ)
    (P Q : ℝ → ℝ → ℂ) (p q : ℝ → ℂ) {a b : ℝ} (hab : a≤b)
    (hjump : ∀x∈Icc a b,
      Tendsto jump (𝓝[{z:ℂ | 0<z.im}] (x:ℂ)) (𝓝 0))
    (hp : ∀x∈Icc a b,Tendsto (fun t=>P t x) (𝓝[>] (0:ℝ)) (𝓝 (p x)))
    (hq : ∀x∈Icc a b,Tendsto (fun t=>Q t x) (𝓝[>] (0:ℝ)) (𝓝 (q x)))
    (hderiv : ∀ᶠt in 𝓝[>] (0:ℝ),∀x∈Icc a b,
      HasDerivWithinAt (fun x=>P t x-Q t x)
        (jump ((x:ℂ)+Complex.I*t)) (Icc a b) x) :
    ∃c:ℂ,∀x∈Icc a b,p x=q x+c := by
  have hh := horizontal_trace_constant jump (fun t x=>P t x-Q t x)
    (fun x=>p x-q x) hab hjump (fun x hx=>(hp x hx).sub (hq x hx)) hderiv
  refine ⟨p a-q a,?_⟩
  intro x hx
  have he := hh x hx
  linear_combination he
end VanishingDerivativeTrace318
