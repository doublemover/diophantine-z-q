module
public import Mathlib.Topology.Connected.Basic
public section

namespace OriginalUpperClosedMapFibreConnected318

open Set

universe u v
variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- The proper-map transfer needed for actual Rees fibres. Unlike the stock
injective closed-map lemma, separated tests upstairs may have intersecting
images: use connectedness of the single fibre over that intersection. -/
theorem preimage {f : A → B} (hclosed : IsClosedMap f) {s : Set B}
    (hs : IsPreconnected s) (hcover : s ⊆ Set.range f)
    (hpoint : ∀ y ∈ s, IsPreconnected (f ⁻¹' ({y} : Set B))) :
    IsPreconnected (f ⁻¹' s) := by
  refine isPreconnected_closed_iff.mpr ?_
  intro U V hU hV hUV hneU hneV
  have him : s ⊆ f '' U ∪ f '' V := by
    intro y hy
    obtain ⟨a, ha⟩ := hcover hy
    have has : a ∈ f ⁻¹' s := by
      change f a ∈ s
      exact ha.symm ▸ hy
    rcases hUV has with hu | hv
    · exact Or.inl ⟨a, hu, ha⟩
    · exact Or.inr ⟨a, hv, ha⟩
  have himU : (s ∩ f '' U).Nonempty := by
    obtain ⟨a, has, haU⟩ := hneU
    exact ⟨f a, has, ⟨a, haU, rfl⟩⟩
  have himV : (s ∩ f '' V).Nonempty := by
    obtain ⟨a, has, haV⟩ := hneV
    exact ⟨f a, has, ⟨a, haV, rfl⟩⟩
  obtain ⟨y, hys, ⟨a, haU, ha⟩, ⟨b, hbV, hb⟩⟩ :=
    isPreconnected_closed_iff.mp hs _ _ (hclosed _ hU) (hclosed _ hV) him himU himV
  have hsub : f ⁻¹' ({y} : Set B) ⊆ f ⁻¹' s := by
    intro x hx
    change f x = y at hx
    change f x ∈ s
    exact hx.symm ▸ hys
  obtain ⟨x, hxy, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp (hpoint y hys) _ _ hU hV (hsub.trans hUV)
      ⟨a, ha, haU⟩ ⟨b, hb, hbV⟩
  exact ⟨x, hsub hxy, hxU, hxV⟩

end OriginalUpperClosedMapFibreConnected318

#print axioms OriginalUpperClosedMapFibreConnected318.preimage
