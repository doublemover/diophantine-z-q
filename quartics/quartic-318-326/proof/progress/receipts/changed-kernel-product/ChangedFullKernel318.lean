module
public import ChangedKernelProductScheme318
public section
noncomputable section
namespace ChangedFullKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "a" => algebraMap R S
local notation "A" => a (OpenJAffineScheme318.A N)
local notation "B" => a (OpenJAffineScheme318.B N)
local notation "hD" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S)
  (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
local notation "K" => ActualLiteralKernelBaseChange318.fiber N S

section ExplicitInverse
variable [Invertible (3:S)]
local notation "T" => ThreeTorsionAlgebra318.Ring A B hD
@[expose] def coproductIso : K ≅ (ThreeTorsionScheme318.scheme A B hD ⨿ Spec (CommRingCat.of S)) :=
  ChangedKernelProductScheme318.iso N S ≪≫ (asIso (coprodSpec T S)).symm
@[reassoc] theorem inl_inv : coprod.inl ≫ (coproductIso N S).inv=ThreeTorsionTriplingFiber318.toFiber A B hD := by
  simp only [coproductIso,Iso.trans_inv,Iso.symm_inv,asIso_hom,←Category.assoc]
  exact (congrArg (fun f=>f ≫ (ChangedKernelProductScheme318.iso N S).inv)
    (coprodSpec_inl T S)).trans (ChangedKernelProductScheme318.finite_inv N S)
@[reassoc] theorem inr_inv : coprod.inr ≫ (coproductIso N S).inv=ChangedKernelProjection318.zero N S := by
  simp only [coproductIso,Iso.trans_inv,Iso.symm_inv,asIso_hom,←Category.assoc]
  exact (congrArg (fun f=>f ≫ (ChangedKernelProductScheme318.iso N S).inv)
    (coprodSpec_inr T S)).trans (ChangedKernelProductScheme318.zero_inv N S)
end ExplicitInverse

/-- The whole actual tripling kernel after every Base N-algebra extension
is exactly the original mapped primitive Scheme plus the actual zero base. -/
@[expose] def iso : K ≅ (CanonicalChangedPrimitive318.scheme N S ⨿ Spec (CommRingCat.of S)) := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact coproductIso N S
@[expose] def finiteInclusion : CanonicalChangedPrimitive318.scheme N S ⟶ K := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionTriplingFiber318.toFiber A B hD
@[reassoc] theorem inl_iso_inv : coprod.inl ≫ (iso N S).inv=finiteInclusion N S := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact inl_inv N S
@[reassoc] theorem inr_iso_inv : coprod.inr ≫ (iso N S).inv=ChangedKernelProjection318.zero N S := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact inr_inv N S
@[reassoc] theorem finiteInclusion_curve : finiteInclusion N S ≫
    pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B)=
      CanonicalChangedPrimitive318.inclusion N S := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionTriplingFiber318.toFiber_fst A B hD
@[reassoc] theorem finiteInclusion_base : finiteInclusion N S ≫ ActualLiteralKernelBaseChange318.structureMap N S=
    CanonicalChangedPrimitive318.structureMap N S := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionTriplingFiber318.toFiber_snd A B hD
end ChangedFullKernel318
