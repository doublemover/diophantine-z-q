module
public import PELMaximalSquaredLocalFibers318
public import Mathlib.Topology.Maps.OpenQuotient
public section
noncomputable section
namespace OpenQuotientSameFibers318
open Topology
set_option maxHeartbeats 1700000
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[expose] def descend (q : X→Y) (f : X→Z) (hq : Function.Surjective q) (y : Y) : Z :=
  f (Classical.choose (hq y))

theorem descend_value (q : X→Y) (f : X→Z) (hq : Function.Surjective q)
    (h : ∀ x y,q x=q y → f x=f y) (x : X) : descend q f hq (q x)=f x :=
  h _ _ (Classical.choose_spec (hq (q x)))

/-- Two actual quotient maps with the SAME fibers give a homeomorphism of
their actual targets. Continuity in both directions is derived by descent. -/
@[expose] def homeomorph (q : X→Y) (f : X→Z) (hq : IsQuotientMap q) (hf : IsQuotientMap f)
    (h : ∀ x y,q x=q y ↔ f x=f y) : Y≃ₜZ where
  toFun := descend q f hq.surjective
  invFun := descend f q hf.surjective
  left_inv y := by
    obtain ⟨x,rfl⟩ := hq.surjective y
    rw [descend_value q f hq.surjective (fun x y => (h x y).mp),
      descend_value f q hf.surjective (fun x y => (h x y).mpr)]
  right_inv z := by
    obtain ⟨x,rfl⟩ := hf.surjective z
    rw [descend_value f q hf.surjective (fun x y => (h x y).mpr),
      descend_value q f hq.surjective (fun x y => (h x y).mp)]
  continuous_toFun := by
    apply hq.continuous_iff.mpr
    have he : (descend q f hq.surjective) ∘ q=f :=
      funext (descend_value q f hq.surjective (fun x y => (h x y).mp))
    rw [he]
    exact hf.continuous
  continuous_invFun := by
    apply hf.continuous_iff.mpr
    have he : (descend f q hf.surjective) ∘ f=q :=
      funext (descend_value f q hf.surjective (fun x y => (h x y).mpr))
    rw [he]
    exact hq.continuous

theorem homeomorph_value (q : X→Y) (f : X→Z) (hq : IsQuotientMap q) (hf : IsQuotientMap f)
    (h : ∀ x y,q x=q y ↔ f x=f y) (x : X) : homeomorph q f hq hf h (q x)=f x :=
  descend_value q f hq.surjective (fun x y => (h x y).mp) x

@[expose] def imageMap (f : X→Y) (U : Set X) : U→f '' U :=
  fun x => ⟨f x,⟨x,x.property,rfl⟩⟩

theorem imageMap_surjective (f : X→Y) (U : Set X) : Function.Surjective (imageMap f U) := by
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem imageMap_openQuotient (f : X→Y) (U : Set X) (hc : ContinuousOn f U)
    (ho : IsOpenMap (fun x : U => f x)) : IsOpenQuotientMap (imageMap f U) where
  surjective := imageMap_surjective f U
  continuous := by
    have h : Continuous (fun x : U => f x) := continuousOn_iff_continuous_restrict.mp hc
    exact h.subtype_mk _
  isOpenMap := ho.subtype_mk _
end OpenQuotientSameFibers318
