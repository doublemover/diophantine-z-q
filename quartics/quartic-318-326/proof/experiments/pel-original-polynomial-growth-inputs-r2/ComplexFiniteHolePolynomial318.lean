module
public import ComplexPolynomialGrowth318
public import Mathlib.Analysis.Complex.RemovableSingularity
public section
noncomputable section
namespace ComplexFiniteHolePolynomial318
open Set Filter
open scoped Topology

/-- A bounded punctured holomorphic coordinate has a constructed analytic
extension. Continuity at the missing point is a conclusion, not an input. -/
theorem bounded_extension {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c,DifferentiableAt ℂ f z)
    (B : ℝ) (hb : ∀ᶠ z in 𝓝[≠] c,‖f z‖≤B) :
    ∃ g : ℂ → ℂ,AnalyticAt ℂ g c ∧ g =ᶠ[𝓝[≠] c] f ∧
      Tendsto f (𝓝[≠] c) (𝓝 (g c)) := by
  have hbound : IsBoundedUnder (·≤·) (𝓝[≠] c) (fun z => ‖f z-f c‖) := by
    refine ⟨B+‖f c‖,?_⟩
    filter_upwards [hb] with z hz
    exact (norm_sub_le _ _).trans (add_le_add_right hz _)
  have ht := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hbound
  let g : ℂ → ℂ := Function.update f c (limUnder (𝓝[≠] c) f)
  have hc : ContinuousAt g c := continuousAt_Function.update_same.mpr ht
  have hg : g =ᶠ[𝓝[≠] c] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [g,Function.update_of_ne hz]
  have hdg : ∀ᶠ z in 𝓝[≠] c,DifferentiableAt ℂ g z := by
    filter_upwards [hd,self_mem_nhdsWithin] with z hz hzc
    apply hz.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hzc] with w hw
    simp only [g,Function.update_of_ne hw]
  refine ⟨g,Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdg hc,hg,?_⟩
  simpa only [g,Function.update_same] using ht


/-- Bounded holomorphy off a finite set constructs a global entire
extension, with the SAME continuous pointwise bound retained at every hole.
Continuity and values at the holes are conclusions, never premises. -/
theorem exists_entire_extension (S : Set ℂ) (hS : S.Finite)
    (f : ℂ → ℂ) (b : ℂ → ℝ) (hbcont : Continuous b)
    (hf : ∀ z ∉ S, DifferentiableAt ℂ f z)
    (hb : ∀ z ∉ S, ‖f z‖ ≤ b z) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z ∉ S, F z = f z) ∧ ∀ z, ‖F z‖ ≤ b z := by
  classical
  have havoid (c : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ∉ S := by
    have hn : (S \ {c})ᶜ ∈ 𝓝 c :=
      (hS.diff {c}).isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hn,self_mem_nhdsWithin] with z hz hzc
    exact fun h => hz ⟨h,hzc⟩
  have hex (c : ℂ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      g =ᶠ[𝓝[≠] c] f ∧ Tendsto f (𝓝[≠] c) (𝓝 (g c)) := by
    have hd := (havoid c).mono (fun z hz => hf z hz)
    have hn : ∀ᶠ z in 𝓝 c, b z < b c + 1 :=
      hbcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    apply bounded_extension hd (b c + 1)
    filter_upwards [havoid c,eventually_nhdsWithin_of_eventually_nhds hn] with z hz hbz
    exact (hb z hz).trans hbz.le
  choose g hg he hlim using hex
  let F : ℂ → ℂ := fun c => g c c
  have hagree (c : ℂ) (hc : c ∉ S) : F c = f c :=
    tendsto_nhds_unique (hlim c) ((hf c hc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hF (c : ℂ) : DifferentiableAt ℂ F c := by
    apply (hg c).differentiableAt.congr_of_eventuallyEq
    have hn : (S \ {c})ᶜ ∈ 𝓝 c :=
      (hS.diff {c}).isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hn,eventually_nhdsWithin_iff.mp (he c)] with z hz hez
    by_cases hzc : z = c
    · subst z
      rfl
    · exact (hagree z (fun h => hz ⟨h,hzc⟩)).trans (hez hzc).symm
  refine ⟨F,hF,hagree,?_⟩
  intro c
  have hl : Tendsto (fun z => ‖f z‖ - b z) (𝓝[≠] c) (𝓝 (‖F c‖ - b c)) :=
    (hlim c).norm.sub (hbcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hn : ‖F c‖ - b c ≤ 0 :=
    le_of_tendsto hl ((havoid c).mono (fun z hz => sub_nonpos.mpr (hb z hz)))
  linarith

/-- A polynomial-growth holomorphic function off finitely many holes is
represented there by an actual polynomial of the uniformly bounded degree. -/
theorem exists_polynomial (S : Set ℂ) (hS : S.Finite)
    (f : ℂ → ℂ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∉ S, DifferentiableAt ℂ f z)
    (hb : ∀ z ∉ S, ‖f z‖ ≤ C * (1 + ‖z‖)^N) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z ∉ S, p.eval z = f z := by
  obtain ⟨F,hF,he,hbF⟩ := exists_entire_extension S hS f
    (fun z => C * (1+‖z‖)^N) (by fun_prop) hf hb
  have hbound (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ = R) :
      ‖F z‖ ≤ (C * 2^N) * R^N := by
    calc
      ‖F z‖ ≤ C * (1+‖z‖)^N := hbF z
      _ ≤ C * (2*R)^N := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by rw [hz]; linarith) N) hC
      _ = (C * 2^N) * R^N := by rw [mul_pow]; ring
  obtain ⟨p,hp,hpe⟩ := ComplexPolynomialGrowth318.exists_polynomial F hF N
    (C*2^N) (by positivity) hbound
  exact ⟨p,hp,fun z hz => (hpe z).trans (he z hz)⟩
end ComplexFiniteHolePolynomial318
