module
public import OriginalHodgeIdealFromFull33_318
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section

namespace OriginalHodgeModuleOverlap318
open NumberField
open scoped TensorProduct nonZeroDivisors

section Read
variable {S C E M : Type*} [CommRing S] [CommRing C] [Field E]
  [Algebra S C] [Algebra C E] [Algebra S E] [IsScalarTower S C E]
  [AddCommGroup M] [Module S M]

/-- Extend the same generic-wedge reading to the actual level-33 overlap. -/
def read (f : M→ₗ[S]E) : C⊗[S]M →ₗ[C] E :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton C (M→ₗ[S]E) f)

theorem read_tmul (f : M→ₗ[S]E) (c : C) (m : M) : read f (c⊗ₜ[S]m)=c • f m := by
  rw [read,TensorProduct.AlgebraTensorModule.lift_tmul,LinearMap.toSpanSingleton_apply,LinearMap.smul_apply]

theorem read_range (f : M→ₗ[S]E) : (read (C:=C) f).range=Submodule.span C (f.range:Set E) := by
  apply le_antisymm
  · rintro x ⟨t,rfl⟩
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul c m => rw [read_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨m,rfl⟩
    exact ⟨1⊗ₜ[S]m,by rw [read_tmul,one_smul]⟩
end Read

variable {E : Type*} [Field E] [NumberField E]

/-- The actual full-33 pullback is an isomorphism of the two marked
Hodge modules compatible with their reading in a common generic wedge.
This constructs all finite generators and the overlap SPAN equality,
as well as the global ideal. No mathematical use of an isogeny here. -/
theorem from_modules
    (S3 S11 C : Type*) [CommRing S3] [CommRing S11] [CommRing C]
    [Algebra (𝓞 E) S3] [Algebra (𝓞 E) S11] [Algebra (𝓞 E) C]
    [Algebra S3 E] [Algebra S11 E] [Algebra C E] [Algebra S3 C] [Algebra S11 C]
    [IsScalarTower (𝓞 E) S3 E] [IsScalarTower (𝓞 E) S11 E] [IsScalarTower (𝓞 E) C E]
    [IsScalarTower S3 C E] [IsScalarTower S11 C E]
    [IsLocalization.Away (3:𝓞 E) S3] [IsLocalization.Away (11:𝓞 E) S11]
    [IsLocalization.Away (33:𝓞 E) C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S3 M] [Module S11 N]
    [Module.Finite S3 M] [Module.Finite S11 N]
    (f : M→ₗ[S3]E) (g : N→ₗ[S11]E) (nz : ∃m,f m≠0)
    (mark : C⊗[S3]M ≃ₗ[C] C⊗[S11]N)
    (comm : (read (C:=C) g).comp mark.toLinearMap=read f) :
    ∃ I : FractionalIdeal (𝓞 E)⁰ E,I≠0 ∧
      (I:Submodule (𝓞 E) E)=f.range.restrictScalars (𝓞 E) ⊓ g.range.restrictScalars (𝓞 E) ∧
      Submodule.span S3 (I:Set E)=f.range ∧ Submodule.span S11 (I:Set E)=g.range := by
  classical
  obtain ⟨G,hG⟩ := Submodule.fg_range f
  obtain ⟨J,hJ⟩ := Submodule.fg_range g
  have hrange : (read (C:=C) f).range=(read (C:=C) g).range := by
    ext x
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨mark m,DFunLike.congr_fun comm m⟩
    · rintro ⟨n,rfl⟩
      refine ⟨mark.symm n,?_⟩
      have h := (DFunLike.congr_fun comm (mark.symm n)).symm
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using h
  rw [read_range,read_range] at hrange
  have equal : Submodule.span C (G:Set E)=Submodule.span C (J:Set E) := by
    rw [←Submodule.span_span_of_tower S3 C (G:Set E),hG,hrange,←hJ,Submodule.span_span_of_tower]
  have nonzero : ∃x∈G,x≠0 := by
    by_contra! all
    have bot : Submodule.span S3 (G:Set E)≤⊥ := Submodule.span_le.mpr (fun x hx => all x hx)
    obtain ⟨m,nm⟩ := nz
    have hm : f m∈Submodule.span S3 (G:Set E) := hG.symm ▸ (show f m∈f.range from ⟨m,rfl⟩)
    exact nm (bot hm)
  obtain ⟨I,ni,inter,left,right⟩ :=
    OriginalHodgeIdealFromFull33_318.build S3 S11 C G J nonzero equal
  rw [hG,hJ] at inter
  exact ⟨I,ni,inter,left.trans hG,right.trans hJ⟩

end OriginalHodgeModuleOverlap318
