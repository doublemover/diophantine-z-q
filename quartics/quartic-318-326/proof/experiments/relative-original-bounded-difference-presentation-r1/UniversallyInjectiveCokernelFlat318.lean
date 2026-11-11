module
public import FlatCokernelDiagram318
public import Mathlib.RingTheory.Flat.Basic
public section
namespace UniversallyInjectiveCokernelFlat318
universe u
open TensorProduct
variable {R A B Q : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup Q]
  [Module R A] [Module R B] [Module R Q]

/-- A genuine flat-cokernel criterion, proved by tensor right-exactness
and a diagram chase. The hypothesis quantifies over ALL modules, not
only residue fields. No fieldwise-to-universal inference is hidden. -/
lemma flat (f : A →ₗ[R] B) (q : B →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat R B]
    (hf : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Injective (f.lTensor N)) : Module.Flat R Q := by
  apply (Module.Flat.iff_rTensor_preserves_injective_linearMap).mpr
  intro N N' _ _ _ _ g hg
  let P := N' ⧸ LinearMap.range g
  let π : N' →ₗ[R] P := Submodule.mkQ (LinearMap.range g)
  have heπ : Function.Exact g π := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hcol := _root_.rTensor_exact A heπ hπ
  have hrow := _root_.lTensor_exact N' he hq
  have hqf : (q.lTensor N).comp (f.lTensor N) = 0 := by
    rw [← LinearMap.lTensor_comp, he.linearMap_comp_eq_zero,
      LinearMap.lTensor_zero]
  have hbb : (π.rTensor B).comp (g.rTensor B) = 0 := by
    rw [← LinearMap.rTensor_comp, heπ.linearMap_comp_eq_zero,
      LinearMap.rTensor_zero]
  apply FlatCokernelDiagram318.injective_cokernel_map
    (f.lTensor N) (f.lTensor N') (f.lTensor P)
    (q.lTensor N) (q.lTensor N')
    (g.rTensor A) (π.rTensor A) (g.rTensor B) (π.rTensor B)
    (g.rTensor Q) (LinearMap.lTensor_surjective N hq)
    hrow hcol hqf hbb
  · ext n a
    simp
  · ext n b
    simp
  · ext n a
    simp
  · exact Module.Flat.rTensor_preserves_injective_linearMap g hg
  · exact hf P
end UniversallyInjectiveCokernelFlat318
