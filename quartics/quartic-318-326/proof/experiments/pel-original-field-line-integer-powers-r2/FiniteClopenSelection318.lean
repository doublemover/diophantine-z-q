module
public import Mathlib.Topology.Constructions
public section
noncomputable section
namespace FiniteClopenSelection318
open Set Filter
open scoped Topology

/-- Membership in a genuinely clopen subset is simultaneously constant
along any finite family of continuous maps near the same point. -/
theorem exists_selection_neighborhood {I X Y : Type*} [Finite I]
    [TopologicalSpace X] [TopologicalSpace Y] (f : I → X → Y)
    (hf : ∀ i, Continuous (f i)) (S : Set Y) (ho : IsOpen S) (hc : IsClosed S)
    (x : X) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ w ∈ V, ∀ i, f i w ∈ S ↔ f i x ∈ S := by
  classical
  have hi (i : I) : ∀ᶠ w in 𝓝 x, f i w ∈ S ↔ f i x ∈ S := by
    by_cases hx : f i x ∈ S
    · filter_upwards [(hf i).continuousAt.eventually (ho.mem_nhds hx)] with w hw
      exact iff_of_true hw hx
    · have hx' : f i x ∈ Sᶜ := hx
      filter_upwards [(hf i).continuousAt.eventually (hc.isOpen_compl.mem_nhds hx')] with w hw
      exact iff_of_false hw hx
  obtain ⟨V,hV,hVo,hVx⟩ := eventually_nhds_iff.mp (Filter.eventually_all.mpr hi)
  exact ⟨V,hVo,hVx,hV⟩
end FiniteClopenSelection318
