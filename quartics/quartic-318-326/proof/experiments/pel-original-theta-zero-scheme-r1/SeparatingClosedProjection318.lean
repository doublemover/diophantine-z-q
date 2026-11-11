module
public import Mathlib.Topology.Maps.Proper.Basic
public section
noncomputable section
namespace SeparatingClosedProjection318
open Set
variable {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]

/-- A closed surjection to an open projected model transfers local
openness at any point whose actual fiber is a singleton. In applications
the separating model may be chosen separately at each original point. -/
theorem neighborhood_image (f : X → Y) (g : Y → B)
    (hf : IsClosedMap f) (hs : Function.Surjective f) (hg : IsOpenMap g)
    (x : X) (hx : ∀ x', f x' = f x → x' = x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set B, IsOpen V ∧ g (f x) ∈ V ∧ V ⊆ (g ∘ f) '' U := by
  let W : Set Y := (f '' Uᶜ)ᶜ
  have hW : IsOpen W := (hf _ hU.isClosed_compl).isOpen_compl
  have hxW : f x ∈ W := by
    rintro ⟨x',hx',hxx⟩
    exact hx' ((hx x' hxx).symm ▸ hxU)
  refine ⟨g '' W,hg W hW,⟨f x,hxW,rfl⟩,?_⟩
  rintro b ⟨y,hy,rfl⟩
  obtain ⟨x',rfl⟩ := hs y
  have hx'U : x' ∈ U := by
    by_contra hn
    exact hy ⟨x',hn,rfl⟩
  exact ⟨x',hx'U,rfl⟩

/-- Properness of the original base projection makes any continuous
factorization through a Hausdorff model closed. This avoids assuming
properness of a separately chosen primitive model. -/
theorem neighborhood_image_of_proper [T2Space Y]
    (f : X → Y) (g : Y → B) (hf : Continuous f) (hg : Continuous g)
    (hp : IsProperMap (g ∘ f)) (honto : Function.Surjective f) (hopen : IsOpenMap g)
    (x : X) (hx : ∀ x', f x' = f x → x' = x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set B, IsOpen V ∧ g (f x) ∈ V ∧ V ⊆ (g ∘ f) '' U :=
  neighborhood_image f g (isProperMap_of_comp_of_t2 hf hg hp).isClosedMap
    honto hopen x hx U hU hxU
end SeparatingClosedProjection318
