module
public import LocalConformalEdgeExtension318
public section
noncomputable section
namespace CanonicalBoundaryTrace318
open Set Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 2800000

/-- The canonical ORIGINAL-domain limit. It will only be used where its
existence is proved, not as an assumed continuous boundary extension. -/
@[expose] def value (D:Set ℂ) (f:ℂ→ℂ) (z:ℂ) : ℂ := limUnder (𝓝[D] z) f

theorem value_eq_of_limit (D:Set ℂ) (f:ℂ→ℂ) {z L:ℂ}
    (hz:z∈closure D) (ht:Tendsto f (𝓝[D] z) (𝓝 L)) : value D f z=L := by
  haveI : NeBot (𝓝[D] z) := mem_closure_iff_nhdsWithin_neBot.mp hz
  exact ht.limUnder_eq

theorem value_eq_on_open (D:Set ℂ) (f:ℂ→ℂ) {z:ℂ} (hz:z∈D)
    (hf:ContinuousWithinAt f D z) : value D f z=f z :=
  value_eq_of_limit D f (subset_closure hz) hf.tendsto

theorem limit_from_germ (D:Set ℂ) (f F:ℂ→ℂ) {z:ℂ}
    (hF:ContinuousAt F z) (he:F=ᶠ[𝓝[D] z] f) :
    Tendsto f (𝓝[D] z) (𝓝 (F z)) :=
  (tendsto_congr' he).mp (hF.tendsto.mono_left nhdsWithin_le_nhds)

/-- A constructed analytic extension controls the canonical values at
ALL nearby closure points, not just at the chosen center. This proves
compatibility of independently constructed edge germs. -/
theorem canonical_near_germ (D:Set ℂ) (f F:ℂ→ℂ) {z:ℂ}
    (hF:AnalyticAt ℂ F z) (he:F=ᶠ[𝓝[D] z] f) :
    ∀ᶠw in 𝓝 z,w∈closure D → value D f w=F w := by
  let S:Set ℂ := {w | w∈D → F w=f w}
  have hzS:z∈interior S := mem_interior_iff_mem_nhds.mpr (eventually_nhdsWithin_iff.mp he)
  filter_upwards [isOpen_interior.mem_nhds hzS,hF.eventually_analyticAt] with w hw ha
  intro hwD
  have hew:F=ᶠ[𝓝[D] w] f := by
    apply eventually_nhdsWithin_iff.mpr
    exact mem_of_superset (isOpen_interior.mem_nhds hw) interior_subset
  exact value_eq_of_limit D f hwD (limit_from_germ D f F ha.continuousAt hew)

/-- Continuity of the canonical trace on the actual closure is a
conclusion of the local analytic construction and genuine limit identity. -/
theorem canonical_continuousWithin (D:Set ℂ) (f F:ℂ→ℂ) {z:ℂ}
    (hz:z∈closure D) (hF:AnalyticAt ℂ F z) (he:F=ᶠ[𝓝[D] z] f) :
    ContinuousWithinAt (value D f) (closure D) z := by
  have hv:=value_eq_of_limit D f hz (limit_from_germ D f F hF.continuousAt he)
  have hnear:(value D f)=ᶠ[𝓝[closure D] z] F :=
    eventually_nhdsWithin_iff.mpr (canonical_near_germ D f F hF he)
  change Tendsto (value D f) (𝓝[closure D] z) (𝓝 (value D f z))
  rw [hv]
  exact (tendsto_congr' hnear).mpr (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

@[expose] def mirror (z:ℂ) : ℂ := -conj z
lemma mirror_involutive (z:ℂ) : mirror (mirror z)=z := by simp [mirror]
lemma mirror_continuous : Continuous mirror :=
  (show Continuous (conj:ℂ→ℂ) from continuous_star).neg

/-- Exact interior mirror symmetry passes to the CONSTRUCTED original
boundary limits. No arbitrary choices of extension germs enter the result. -/
theorem reflected_limit (D:Set ℂ) (hD:∀z:ℂ,mirror z∈D ↔ z∈D)
    (f:ℂ→ℂ) (hf:∀z∈D,f (mirror z)=mirror (f z))
    {z L:ℂ} (ht:Tendsto f (𝓝[D] z) (𝓝 L)) :
    Tendsto f (𝓝[D] (mirror z)) (𝓝 (mirror L)) := by
  have hto:Tendsto mirror (𝓝[D] (mirror z)) (𝓝[D] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mirror_involutive] using
        (mirror_continuous.tendsto (mirror z)).mono_left nhdsWithin_le_nhds
    · exact self_mem_nhdsWithin.mono (fun w hw=>(hD w).mpr hw)
  have hcomp:=mirror_continuous.continuousAt.tendsto.comp (ht.comp hto)
  apply (tendsto_congr' ?_).mp hcomp
  filter_upwards [self_mem_nhdsWithin] with w hw
  change mirror (f (mirror w))=f w
  rw [hf w hw,mirror_involutive]

theorem canonical_reflection (D:Set ℂ) (hD:∀z:ℂ,mirror z∈D ↔ z∈D)
    (f:ℂ→ℂ) (hf:∀z∈D,f (mirror z)=mirror (f z))
    {z L:ℂ} (hz:z∈closure D) (hσ:mirror z∈closure D)
    (ht:Tendsto f (𝓝[D] z) (𝓝 L)) :
    value D f (mirror z)=mirror (value D f z) := by
  rw [value_eq_of_limit D f hz ht]
  exact value_eq_of_limit D f hσ (reflected_limit D hD f hf ht)
end CanonicalBoundaryTrace318
