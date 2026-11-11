module
public import PELOriginalDescendedPeriodTensor318
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public section
noncomputable section
namespace PELOriginalKernelDeterminantLine318
open QuaternionicRealPeriod318 PELOriginalFlatPeriodKernel318
open PELOriginalKernelMonodromyCovariance318 PELOriginalFlatSymplecticTransport318
open PELOriginalFlatPeriodSquare318

/-- Genuine exterior-square transport, with both inverse maps proved on
the whole exterior power from functoriality. -/
@[expose] def exteriorEquiv {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) :
    (⋀[ℂ]^2 M) ≃ₗ[ℂ] (⋀[ℂ]^2 N) where
  toFun := exteriorPower.map 2 e.toLinearMap
  invFun := exteriorPower.map 2 e.symm.toLinearMap
  left_inv := by
    intro x
    change ((exteriorPower.map 2 e.symm.toLinearMap).comp
      (exteriorPower.map 2 e.toLinearMap)) x=x
    rw [←exteriorPower.map_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by
      ext z;exact e.symm_apply_apply z
    rw [he,exteriorPower.map_id]
    rfl
  right_inv := by
    intro x
    change ((exteriorPower.map 2 e.toLinearMap).comp
      (exteriorPower.map 2 e.symm.toLinearMap)) x=x
    rw [←exteriorPower.map_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by
      ext z;exact e.apply_symm_apply z
    rw [he,exteriorPower.map_id]
    rfl
  map_add' := (exteriorPower.map 2 e.toLinearMap).map_add
  map_smul' := (exteriorPower.map 2 e.toLinearMap).map_smul

@[expose] def kernelFrame (τ : ℂ) : ComplexVectors ≃ₗ[ℂ] LinearMap.ker (periodMap τ) where
  toFun v := ⟨kernelLift τ v,kernelLift_period τ v⟩
  invFun p := p.val.2
  left_inv := by intro v;rfl
  right_inv := by intro p;apply Subtype.ext;exact kernel_recover τ p p.property
  map_add' := by intros;apply Subtype.ext;exact map_add _ _ _
  map_smul' := by intros;apply Subtype.ext;exact map_smul _ _ _

/-- Actual top exterior power of the WHOLE original period-kernel plane,
not an unrelated one-dimensional carrier. -/
abbrev Fiber (τ : ℂ) := ⋀[ℂ]^2 (LinearMap.ker (periodMap τ))
abbrev Coordinates := ⋀[ℂ]^2 ComplexVectors
@[expose] def frame (τ : ℂ) : Coordinates ≃ₗ[ℂ] Fiber τ := exteriorEquiv (kernelFrame τ)
lemma rank_one (τ : ℂ) : Module.finrank ℂ (Fiber τ)=1 := by
  rw [←(frame τ).finrank_eq]
  simp [Coordinates,exteriorPower.finrank_eq,QuaternionicRealPeriod318.ComplexVectors]

/-- Actual monodromy on the intrinsic determinant fibers. -/
@[expose] def transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : Fiber (parameter u τ) ≃ₗ[ℂ] Fiber τ :=
  exteriorEquiv (kernelEquiv u τ hτ)

lemma kernelFrame_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (v : ComplexVectors) :
    kernelEquiv u τ hτ (kernelFrame (parameter u τ) v)=
      kernelFrame τ (coefficientEquiv u τ hτ v) := by
  apply Subtype.ext
  exact (kernel_recover τ _ ((kernel_transport u τ hτ _).mpr
    (kernelLift_period (parameter u τ) v))).symm

/-- The full exterior map agrees with the produced coordinate transition,
checked by the actual universal alternating map, not by comparing dimensions. -/
theorem frame_transport (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    (transport u τ hτ).toLinearMap.comp (frame (parameter u τ)).toLinearMap=
      (frame τ).toLinearMap.comp (exteriorEquiv (coefficientEquiv u τ hτ)).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply,LinearMap.comp_apply]
  change exteriorPower.map 2 (kernelEquiv u τ hτ).toLinearMap
      (exteriorPower.map 2 (kernelFrame (parameter u τ)).toLinearMap (exteriorPower.ιMulti ℂ 2 v))=
    exteriorPower.map 2 (kernelFrame τ).toLinearMap
      (exteriorPower.map 2 (coefficientEquiv u τ hτ).toLinearMap (exteriorPower.ιMulti ℂ 2 v))
  simp only [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact kernelFrame_transport u τ hτ (v i)
end PELOriginalKernelDeterminantLine318
