module
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace OriginalKernelScalarExtension318
open TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (E : Type w) (N : Type z) [AddCommGroup E] [AddCommGroup N] [Module A E] [Module A N]
  (E' : Type t) (N' : Type t) [AddCommGroup E'] [AddCommGroup N'] [Module B E'] [Module B N']
  (q : E →ₗ[A] N) (q' : E' →ₗ[B] N')
  (e : B ⊗[A] E ≃ₗ[B] E') (a : B ⊗[A] N ≃ₗ[B] N')
  (square : q'.comp e.toLinearMap = a.toLinearMap.comp (q.baseChange B))

include square in
lemma unit_zero (x : LinearMap.ker q) : q' (e ((1 : B) ⊗ₜ[A] (x : E))) = 0 := by
  have h := LinearMap.congr_fun square ((1 : B) ⊗ₜ[A] (x : E))
  change q' (e ((1 : B) ⊗ₜ[A] (x : E))) = a ((1 : B) ⊗ₜ[A] q x) at h
  rw [x.property,tmul_zero,map_zero] at h
  exact h

/-- The original source-kernel element mapped by the actual extension
unit and specified source comparison, not a newly selected kernel vector. -/
@[expose] def unit (x : LinearMap.ker q) : LinearMap.ker q' :=
  ⟨e ((1 : B) ⊗ₜ[A] (x : E)),unit_zero A B E N E' N' q q' e a square x⟩

include square in
lemma extended_zero (x : B ⊗[A] LinearMap.ker q) :
    q' (e (((LinearMap.ker q).subtype.baseChange B) x)) = 0 := by
  have h := LinearMap.congr_fun square (((LinearMap.ker q).subtype.baseChange B) x)
  rw [LinearMap.comp_apply,LinearMap.comp_apply] at h
  rw [h]
  have hz : (q.baseChange B) (((LinearMap.ker q).subtype.baseChange B) x) = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul b k =>
      change b ⊗ₜ[A] q (k : E) = 0
      rw [k.property,tmul_zero]
    | add x y hx hy => simpa only [map_add,hx,hy,add_zero]
  rw [hz,map_zero]

@[expose] def map : B ⊗[A] LinearMap.ker q →ₗ[B] LinearMap.ker q' :=
  (e.toLinearMap.comp ((LinearMap.ker q).subtype.baseChange B)).codRestrict
    (LinearMap.ker q') (by
      intro x
      exact extended_zero A B E N E' N' q q' e a square x)

lemma map_tmul (b : B) (x : LinearMap.ker q) :
    map A B E N E' N' q q' e a square (b ⊗ₜ[A] x) =
      b • unit A B E N E' N' q q' e a square x := by
  apply Subtype.ext
  change e (b ⊗ₜ[A] (x : E)) = b • e ((1 : B) ⊗ₜ[A] (x : E))
  rw [← e.map_smul,smul_tmul',smul_eq_mul,mul_one]

include square in
/-- Right exactness alone supplies every original overlap relation from
localized chart relations. Flatness or kernel injectivity is NOT assumed. -/
lemma map_surjective (hq : Function.Surjective q) :
    Function.Surjective (map A B E N E' N' q q' e a square) := by
  intro z
  have hz : (q.baseChange B) (e.symm z) = 0 := by
    apply a.injective
    rw [map_zero]
    have h := LinearMap.congr_fun square (e.symm z)
    simpa only [LinearMap.comp_apply,LinearEquiv.apply_symm_apply,z.property] using h.symm
  have hex := TensorProduct.lTensor_exact B q.exact_subtype_ker_map hq
  have hm : e.symm z ∈ LinearMap.range ((LinearMap.ker q).subtype.lTensor B) := by
    rw [← hex.linearMap_ker_eq]
    exact hz
  obtain ⟨w,hw⟩ := hm
  refine ⟨w,?_⟩
  apply Subtype.ext
  change e (((LinearMap.ker q).subtype.baseChange B) w) = z
  change ((LinearMap.ker q).subtype.baseChange B) w = e.symm z at hw
  rw [hw,LinearEquiv.apply_symm_apply]

include square in
/-- The unchanged chart-kernel image Laurent-spans the SAME overlap
kernel, through the actual original restriction unit. -/
lemma span (hq : Function.Surjective q) :
    Submodule.span B (Set.range (unit A B E N E' N' q q' e a square)) = ⊤ := by
  have hall (w : B ⊗[A] LinearMap.ker q) :
      map A B E N E' N' q q' e a square w ∈
        Submodule.span B (Set.range (unit A B E N E' N' q q' e a square)) := by
    induction w using TensorProduct.inductionOn with
    | tmul b x =>
      rw [map_tmul]
      exact Submodule.smul_mem _ b (Submodule.subset_span ⟨x,rfl⟩)
    | add w z hw hz => simpa only [map_add] using Submodule.add_mem _ hw hz
  apply top_unique
  intro z _
  obtain ⟨w,rfl⟩ := map_surjective A B E N E' N' q q' e a square hq z
  exact hall w
end OriginalKernelScalarExtension318
