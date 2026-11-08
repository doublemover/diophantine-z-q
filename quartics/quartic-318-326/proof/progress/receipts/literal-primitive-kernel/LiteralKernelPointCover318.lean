module
public import LiteralFullKernel318
public section
noncomputable section
namespace LiteralKernelPointCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "Base" => Spec (CommRingCat.of (OpenJModel318.Base N))
local notation "T" => ThreeTorsionScheme318.scheme A B hD
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD

/-- A topological cover obtained from the actual full Scheme coproduct. -/
theorem covers (x:K) : x ∈ Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD) ∨
    x ∈ Set.range (LiteralKernelZeroSection318.toKernel N) := by
  obtain ⟨s,hs⟩:=(coprodMk T Base).surjective ((LiteralFullKernel318.iso N).hom x)
  rcases s with a|b
  · left
    refine ⟨a,?_⟩
    apply (LiteralFullKernel318.iso N).hom.homeomorph.injective
    change (ThreeTorsionTriplingFiber318.toFiber A B hD ≫ (LiteralFullKernel318.iso N).hom) a=_
    rw [LiteralFullKernel318.finite_iso_hom]
    simpa only [coprodMk_inl,Scheme.Hom.homeomorph_apply] using hs
  · right
    refine ⟨b,?_⟩
    apply (LiteralFullKernel318.iso N).hom.homeomorph.injective
    change (LiteralKernelZeroSection318.toKernel N ≫ (LiteralFullKernel318.iso N).hom) b=_
    rw [LiteralFullKernel318.zero_iso_hom]
    simpa only [coprodMk_inr,Scheme.Hom.homeomorph_apply] using hs

lemma disjoint : Disjoint (Set.range (ThreeTorsionTriplingFiber318.toFiber A B hD))
    (Set.range (LiteralKernelZeroSection318.toKernel N)) := by
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ he
  have hh:=congrArg ((LiteralFullKernel318.iso N).hom) he
  change (ThreeTorsionTriplingFiber318.toFiber A B hD ≫ (LiteralFullKernel318.iso N).hom) a=
    (LiteralKernelZeroSection318.toKernel N ≫ (LiteralFullKernel318.iso N).hom) b at hh
  rw [LiteralFullKernel318.finite_iso_hom,LiteralFullKernel318.zero_iso_hom] at hh
  exact inl_ne_inr T Base a b hh
end LiteralKernelPointCover318
