module
public import Mathlib.Topology.Homeomorph.Lemmas
public section
namespace QuotientSingletonOpenEmbedding318
open Set Topology
/-- A quotient map is an open embedding on any open region whose points
have singleton fibers even against points outside that region. -/
theorem restriction {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsQuotientMap f) (U : Set X) (hU : IsOpen U)
    (hu : ∀ x∈U, ∀ y, f x=f y → x=y) :
    IsOpenEmbedding (fun x : U => f x.val) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hf.continuous.comp continuous_subtype_val
  · intro x y h
    exact Subtype.ext (hu x.val x.property y.val h)
  · intro V hV
    let W : Set X := Subtype.val '' V
    have hW : IsOpen W := hU.isOpenMap_subtype_val V hV
    have hs : f ⁻¹' (f '' W)=W := by
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,hzy⟩,hfy⟩
        subst y
        have hzx := hu z.val z.property x hfy
        rw [←hzx]
        exact ⟨z,hz,rfl⟩
      · intro hx
        exact ⟨x,hx,rfl⟩
    have hi : (fun x : U => f x.val) '' V=f '' W := by
      simp only [W,Set.image_image,Function.comp_def]
    rw [hi]
    apply hf.isCoinducing.isOpen_preimage.mp
    rw [hs]
    exact hW
end QuotientSingletonOpenEmbedding318
