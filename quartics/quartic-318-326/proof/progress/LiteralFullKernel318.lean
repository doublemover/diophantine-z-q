module
public import LiteralKernelComplementZero318
public section
noncomputable section
namespace LiteralFullKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "Base" => Spec (CommRingCat.of (OpenJModel318.Base N))
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
local notation "T" => ThreeTorsionScheme318.scheme A B hD

/-- The entire actual literal tripling fiber, not merely its finite or
nonvertical restriction, is the original rank-eight scheme plus the base. -/
@[expose] def iso : K ≅ T ⨿ Base :=
  LiteralKernelComplement318.iso N ≪≫
    asIso (coprod.map (𝟙 T) (LiteralKernelComplementZero318.iso N).hom)

/-- The first coproduct inclusion is exactly the original torsion inclusion
into the actual tripling fiber. -/
@[reassoc] theorem finite_iso_hom : ThreeTorsionTriplingFiber318.toFiber A B hD ≫ (iso N).hom=coprod.inl := by
  simp only [iso,Iso.trans_hom,asIso_hom,←Category.assoc,LiteralKernelComplement318.finite_iso_hom,
    coprod.inl_map,Category.id_comp]

/-- The other inclusion is exactly the actual zero section of the fiber. -/
@[reassoc] theorem zero_iso_hom : LiteralKernelZeroSection318.toKernel N ≫ (iso N).hom=coprod.inr := by
  rw [←LiteralKernelZeroSection318.intoComplement_inclusion]
  simp only [iso,Iso.trans_hom,asIso_hom,Category.assoc]
  rw [←Category.assoc (LiteralKernelComplement318.inclusion N),LiteralKernelComplement318.complement_iso_hom,
    coprod.inr_map,←Category.assoc,LiteralKernelComplementZero318.iso_hom,
    LiteralKernelZeroSection318.section_retraction,Category.id_comp]

@[reassoc] theorem inl_iso_inv : coprod.inl ≫ (iso N).inv=ThreeTorsionTriplingFiber318.toFiber A B hD := by
  rw [←finite_iso_hom N,Category.assoc,Iso.hom_inv_id,Category.comp_id]
@[reassoc] theorem inr_iso_inv : coprod.inr ≫ (iso N).inv=LiteralKernelZeroSection318.toKernel N := by
  rw [←zero_iso_hom N,Category.assoc,Iso.hom_inv_id,Category.comp_id]
end LiteralFullKernel318
