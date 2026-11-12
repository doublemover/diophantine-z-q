module
public import FourCharacterRootRecombination318
public import Mathlib.Topology.MetricSpace.Basic
public section
noncomputable section
namespace FourRootPuncturedRegularity318
open Set Filter
open scoped Topology
open FourCharacterRootRecombination318
lemma denominator_ne_iff (b:Fin 4→ℂ) (t:ℂ):
    denominator b t≠0 ↔ ∀k,t≠b k := by
  simp only [denominator,product,linear,mul_ne_zero_iff,sub_ne_zero]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ k
    fin_cases k <;> assumption
  · intro h
    exact ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩

/-- The actual finite square parameter misses ALL original branch values
on one punctured neighborhood. Distinct branch labels are used for every
other root, not merely the coordinate selected for ramification. -/
theorem finite (b:Fin 4→ℂ) (hb:Function.Injective b) (j:Fin 4):
    ∀ᶠw in 𝓝[≠] (0:ℂ),denominator b (b j+w^2)≠0 := by
  have hk:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),b j+w^2≠b k:=by
    intro k
    by_cases h:k=j
    · subst k
      filter_upwards [self_mem_nhdsWithin] with w hw
      intro he
      have hs:w^2=0:=by linear_combination he
      exact (pow_ne_zero 2 hw) hs
    · have hn:b j-b k≠0:=sub_ne_zero.mpr (fun he=>h (hb he).symm)
      have hc:ContinuousAt (fun w:ℂ=>b j+w^2-b k) 0:=by fun_prop
      have he:∀ᶠw in 𝓝 (0:ℂ),b j+w^2-b k≠0:=
        hc.eventually_ne (by simpa only [zero_pow (by decide:2≠0),add_zero] using hn)
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with w hw
      exact sub_ne_zero.mp hw
  filter_upwards [hk 0,hk 1,hk 2,hk 3] with w h0 h1 h2 h3
  apply (denominator_ne_iff b _).mpr
  intro k
  fin_cases k <;> assumption

/-- The original reciprocal square parameter likewise misses all finite
branch values near infinity; no target chart containment is assumed. -/
theorem infinity (b:Fin 4→ℂ):
    ∀ᶠw in 𝓝[≠] (0:ℂ),denominator b ((w^2)⁻¹)≠0 := by
  have hk:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),(w^2)⁻¹≠b k:=by
    intro k
    have hc:ContinuousAt (fun w:ℂ=>1-b k*w^2) 0:=by fun_prop
    have he:∀ᶠw in 𝓝 (0:ℂ),1-b k*w^2≠0:=hc.eventually_ne (by norm_num)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hn
    intro h
    apply hw
    rw [←h]
    field_simp [hn]
  filter_upwards [hk 0,hk 1,hk 2,hk 3] with w h0 h1 h2 h3
  apply (denominator_ne_iff b _).mpr
  intro k
  fin_cases k <;> assumption
end FourRootPuncturedRegularity318
