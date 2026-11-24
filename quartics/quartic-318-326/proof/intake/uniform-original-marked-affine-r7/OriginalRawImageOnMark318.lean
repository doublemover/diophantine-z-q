module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.Submodule.Pointwise
public section
open scoped TensorProduct Pointwise
namespace OriginalRawImageOnMark318
variable {A S L D : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup L] [Module A L] [AddCommGroup D] [Module A D]

/-- At a literal marked point, the map from the integral arithmetic model
need not be flat. Nonetheless, a raw scalar image equality descends
through arbitrary scalar extension; in residue characteristic dividing
the scalar the right side is zero, not an inverse to zero. -/
theorem baseChange (f : L→ₗ[A]D) (a : A)
    (image : f.range=a • (⊤:Submodule A D)) :
    (f.baseChange S).range=(algebraMap A S a) • (⊤:Submodule S (S⊗[A]D)) := by
  have scale (s : S) (d : D) :
      s⊗ₜ[A](a • d) = (algebraMap A S a) • (s⊗ₜ[A]d) := by
    rw [←TensorProduct.smul_tmul, ←TensorProduct.smul_tmul', algebraMap_smul]
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul s l =>
      obtain ⟨d,_,h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ a (⊤:Submodule A D)).mp
        (image ▸ LinearMap.mem_range_self f l)
      rw [LinearMap.baseChange_tmul,←h,scale]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    clear hx hz
    induction z using TensorProduct.inductionOn with
    | tmul s d =>
      have h : a • d∈f.range := image ▸ Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
      obtain ⟨l,hl⟩ := h
      exact ⟨s⊗ₜ[A]l, by rw [LinearMap.baseChange_tmul,hl,scale]⟩
    | add x y hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy

end OriginalRawImageOnMark318
