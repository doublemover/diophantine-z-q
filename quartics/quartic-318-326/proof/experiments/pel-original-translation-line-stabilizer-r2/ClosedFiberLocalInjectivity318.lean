module
public import Mathlib.Topology.Maps.Proper.Basic
public section
noncomputable section
namespace ClosedFiberLocalInjectivity318
open Set
variable {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed surjection with a singleton fiber transfers local
injectivity of the original projection to the ENTIRE intermediate
model near that fiber. Every intermediate point is lifted, not only
points chosen from one original branch. -/
theorem transfer (f : X → Y) (p : Y → B) (hf : IsClosedMap f)
    (hs : Function.Surjective f) (x : X)
    (hfx : ∀ x', f x' = f x → x' = x)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U)
    (hinj : Set.InjOn (p ∘ f) U) :
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧ Set.InjOn p V := by
  let V := (f '' Uᶜ)ᶜ
  have hV : IsOpen V := (hf _ hU.isClosed_compl).isOpen_compl
  have hxV : f x ∈ V := by
    rintro ⟨x',hx',he⟩
    exact hx' ((hfx x' he).symm ▸ hxU)
  have hlift : ∀ y ∈ V, ∃ z ∈ U, f z = y := by
    intro y hy
    obtain ⟨z,rfl⟩ := hs y
    refine ⟨z,?_,rfl⟩
    by_contra hz
    exact hy ⟨z,hz,rfl⟩
  refine ⟨V,hV,hxV,?_⟩
  intro y hy y' hy' he
  obtain ⟨z,hz,rfl⟩ := hlift y hy
  obtain ⟨z',hz',rfl⟩ := hlift y' hy'
  exact congrArg f (hinj hz hz' he)
end ClosedFiberLocalInjectivity318
