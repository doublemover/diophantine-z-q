module
public import OriginalPeriodPlaneOverlap318
public section
noncomputable section
namespace OriginalPeriodInfinityIndependentGraphs318
open OriginalPeriodIndependentGraphs318 OriginalPeriodProjectiveModel318
open OriginalPeriodPlaneOverlap318 ComplexAffineFreeTranslation318 Filter
open scoped Topology
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Every point of the original Y=1 chart is smooth. Euler's actual
linear/cubic identity gives v=0 if both partials vanish, contradicting the
unit v-partial there. No period parametrization or generic-point argument. -/
lemma partial_nonzero (p : ℂ × ℂ) (hp : infinityEquation L p=0) :
    1-2*A L*p.1*p.2-3*B L*p.2^2≠0 ∨ -(3*p.1^2+A L*p.2^2)≠0 := by
  by_contra h
  push Not at h
  have hv : p.2=0 := by
    dsimp [infinityEquation] at hp
    linear_combination (3*hp-p.1*h.2-p.2*h.1)/2
  have hh := h.1
  simp only [hv,mul_zero,zero_pow (by decide : 2≠0),sub_zero] at hh
  exact one_ne_zero hh

lemma vertical_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun v : ℂ => infinityEquation L (p.1,v))
      (1-2*A L*p.1*p.2-3*B L*p.2^2) p.2 := by
  convert (((hasDerivAt_id p.2).sub_const (p.1^3)).sub
    (((hasDerivAt_id p.2).pow 2).const_mul (A L*p.1))).sub
      (((hasDerivAt_id p.2).pow 3).const_mul (B L)) using 1 <;>
        simp [infinityEquation] <;> ring
lemma horizontal_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun u : ℂ => infinityEquation L (u,p.2))
      (-(3*p.1^2+A L*p.2^2)) p.1 := by
  convert (((hasDerivAt_const p.1 p.2).sub ((hasDerivAt_id p.1).pow 3)).sub
    (((hasDerivAt_id p.1).const_mul (A L)).mul_const (p.2^2))).sub_const
      (B L*p.2^3) using 1 <;> simp [infinityEquation] <;> ring

/-- Independent implicit graphs cover the ENTIRE original infinity
chart, not just its origin or selected period-image points. -/
theorem graph (p : ℂ × ℂ) (hp : infinityEquation L p=0) :
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.1 ∧ g p.1=p.2 ∧
      (∀ᶠ z in 𝓝 p.1,infinityEquation L (z,g z)=0) ∧
      (∀ᶠ v in 𝓝 p,infinityEquation L v=0 ↔ g v.1=v.2)) ∨
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.2 ∧ g p.2=p.1 ∧
      (∀ᶠ z in 𝓝 p.2,infinityEquation L (g z,z)=0) ∧
      (∀ᶠ v in 𝓝 p,infinityEquation L v=0 ↔ g v.2=v.1)) := by
  rcases partial_nonzero L p hp with hv | hu
  · left
    simpa only [hp] using AnalyticImplicitGraph318.exists_graph
      (infinity_analytic L p) (vertical_derivative L p) hv
  · right
    have hf : AnalyticAt ℂ (fun v : ℂ × ℂ => infinityEquation L (v.2,v.1)) (p.2,p.1) := by
      unfold infinityEquation
      fun_prop
    obtain ⟨g,hg,hval,he,huniq⟩ := AnalyticImplicitGraph318.exists_graph
      hf (horizontal_derivative L p) hu
    refine ⟨g,hg,hval,by simpa only [hp] using he,?_⟩
    have ht : Tendsto (fun v : ℂ × ℂ => (v.2,v.1)) (𝓝 p) (𝓝 (p.2,p.1)) :=
      (by fun_prop : ContinuousAt (fun v : ℂ × ℂ => (v.2,v.1)) p).tendsto
    simpa only [hp] using ht.eventually huniq
end OriginalPeriodInfinityIndependentGraphs318
