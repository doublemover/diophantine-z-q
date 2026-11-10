module
public import AnalyticImplicitGraph318
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public section
noncomputable section
namespace AnalyticZeroLocusChart318
open Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2200000

/-- Actual zero-locus points retain their independently induced ambient
complex-plane topology. No parametrizing source enters this definition. -/
abbrev ZeroLocus (f : ℂ × ℂ → ℂ) := {p : ℂ × ℂ // f p=0}

/-- A genuine independent implicit graph yields an ACTUAL open chart on
the ambient zero locus. The inverse has holomorphic ambient coordinates
on its entire target, not just an unspecified inverse germ at the center. -/
theorem exists_chart (f : ℂ × ℂ → ℂ) (p : ZeroLocus f) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g p.val.1) (hg0 : g p.val.1=p.val.2)
    (he : ∀ᶠ x in 𝓝 p.val.1,f (x,g x)=0)
    (hu : ∀ᶠ v in 𝓝 p.val,f v=0 ↔ g v.1=v.2) :
    ∃ e : OpenPartialHomeomorph (ZeroLocus f) ℂ,
      p∈e.source ∧ (∀q,e q=q.val.1) ∧
      AnalyticOnNhd ℂ (fun x => (e.symm x).val) e.target := by
  obtain ⟨V,hV,hVo,hVp⟩ := eventually_nhds_iff.mp hu
  have ht : Tendsto (fun x => (x,g x)) (𝓝 p.val.1) (𝓝 p.val) := by
    have hh := (continuousAt_id.prodMk hg.continuousAt).tendsto
    simpa only [hg0] using hh
  have hn : ∀ᶠ x in 𝓝 p.val.1,f (x,g x)=0 ∧ (x,g x)∈V ∧ AnalyticAt ℂ g x :=
    he.and ((ht.eventually (hVo.mem_nhds hVp)).and hg.eventually_analyticAt)
  obtain ⟨U,hU,hUo,hUp⟩ := eventually_nhds_iff.mp hn
  let inverse : ℂ → ZeroLocus f := fun x =>
    if hx:x∈U then ⟨(x,g x),(hU x hx).1⟩ else p
  have hi (x : ℂ) (hx : x∈U) : (inverse x).val=(x,g x) := by
    dsimp [inverse]
    rw [dif_pos hx]
  have hgc : ContinuousOn g U := fun x hx => (hU x hx).2.2.continuousAt.continuousWithinAt
  have hic : ContinuousOn inverse U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh : Continuous (fun x : U => (x.val,g x.val)) :=
      continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp hgc)
    have hc := hh.subtype_mk (fun x : U => (hU x.val x.property).1)
    convert hc using 1
    funext x
    apply Subtype.ext
    exact hi x.val x.property
  let e : OpenPartialHomeomorph (ZeroLocus f) ℂ := {
    toFun := fun q => q.val.1
    invFun := inverse
    source := {q | q.val∈V ∧ q.val.1∈U}
    target := U
    map_source' := fun _ hq => hq.2
    map_target' := by
      intro x hx
      change (inverse x).val∈V ∧ (inverse x).val.1∈U
      rw [hi x hx]
      exact ⟨(hU x hx).2.1,hx⟩
    left_inv' := by
      intro q hq
      apply Subtype.ext
      rw [hi _ hq.2]
      exact Prod.ext rfl ((hV q.val hq.1).mp q.property)
    right_inv' := by
      intro x hx
      change (inverse x).val.1=x
      rw [hi x hx]
    open_source := (hVo.preimage continuous_subtype_val).inter
      (hUo.preimage (continuous_fst.comp continuous_subtype_val))
    open_target := hUo
    continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
    continuousOn_invFun := hic }
  refine ⟨e,⟨hVp,hUp⟩,fun _ => rfl,?_⟩
  intro x hx
  have ha : AnalyticAt ℂ (fun z => (z,g z)) x := analyticAt_id.prod (hU x hx).2.2
  apply ha.congr
  filter_upwards [hUo.mem_nhds hx] with y hy
  exact (hi y hy).symm
end AnalyticZeroLocusChart318
