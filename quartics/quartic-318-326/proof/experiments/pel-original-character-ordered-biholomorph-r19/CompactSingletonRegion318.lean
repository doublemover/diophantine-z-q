module
public import QuotientSingletonOpenEmbedding318
public import Mathlib.Topology.Maps.Proper.Basic
public section
namespace CompactSingletonRegion318
open Set Topology
/-- A continuous map from a compact space to a Hausdorff space is an
embedding on any open region whose fibers are singleton against the ENTIRE
compact source. The region need not be open in the ambient target. -/
theorem restriction {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (U : Set X) (hU : IsOpen U)
    (hu : ∀ x∈U, ∀ y, f x=f y → x=y) :
    IsEmbedding (fun x : U => f x.val) := by
  let g : X → Set.range f := fun x => ⟨f x,⟨x,rfl⟩⟩
  have hg : Continuous g := hf.subtype_mk _
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := y.property
    exact ⟨x,Subtype.ext hx⟩
  have hgq : IsQuotientMap g := IsQuotientMap.of_surjective_continuous hgs hg
  have he := QuotientSingletonOpenEmbedding318.restriction g hgq U hU
    (fun x hx y h => hu x hx y (congrArg Subtype.val h))
  exact IsEmbedding.subtypeVal.comp he.toIsEmbedding
end CompactSingletonRegion318
