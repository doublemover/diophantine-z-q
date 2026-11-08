module
public import LiteralKernelNegation318
public import ThreeTorsionNegationScheme318
public import ThreeTorsionDiamond318
public import LiteralFullKernel318
public section
noncomputable section
namespace LiteralKernelDiamond318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

/-- The exact old rank-eight coordinate involution intertwines the actual
canonical map into the actual global kernel with global negation. -/
@[reassoc] theorem finite_compatibility :
    ThreeTorsionNegationScheme318.negation A B hD ≫ ThreeTorsionTriplingFiber318.toFiber A B hD=
      ThreeTorsionTriplingFiber318.toFiber A B hD ≫ LiteralKernelNegation318.negation N := by
  apply pullback.hom_ext
  · simp only [Category.assoc,ThreeTorsionTriplingFiber318.toFiber_fst,
      LiteralKernelNegation318.negation_fst,ThreeTorsionTriplingFiber318.toFiber_fst_assoc,
      ThreeTorsionNegationScheme318.completed_inclusion]
  · simp only [Category.assoc,ThreeTorsionTriplingFiber318.toFiber_snd,
      LiteralKernelNegation318.negation_snd,ThreeTorsionNegationScheme318.over_base]

/-- The full, exact coproduct decomposition is equivariant: original finite
negation on its first summand and the identity on its actual zero summand. -/
theorem coproduct_equivariance :
    LiteralKernelNegation318.negation N ≫ (LiteralFullKernel318.iso N).hom=
      (LiteralFullKernel318.iso N).hom ≫ coprod.map (ThreeTorsionNegationScheme318.negation A B hD) (𝟙 _) := by
  apply (cancel_epi (LiteralFullKernel318.iso N).inv).mp
  apply coprod.hom_ext
  · simp only [←Category.assoc,LiteralFullKernel318.inl_iso_inv]
    rw [←finite_compatibility,Category.assoc,LiteralFullKernel318.finite_iso_hom,
      coprod.inl_map]
  · simp only [←Category.assoc,LiteralFullKernel318.inr_iso_inv]
    rw [LiteralKernelNegation318.zero_fixed,LiteralFullKernel318.zero_iso_hom,
      coprod.inr_map,Category.id_comp]

variable [Nontrivial (OpenJModel318.Base N)]
/-- Compatibility with the previously published nontrivial diamond unit,
not a newly chosen involution on an abstract eight-point set. -/
theorem published_minus_one :
    Spec.map (CommRingCat.ofHom (ThreeTorsionDiamond318.diamond A B hD (-1)).toAlgHom.toRingHom) ≫
      ThreeTorsionTriplingFiber318.toFiber A B hD=
    ThreeTorsionTriplingFiber318.toFiber A B hD ≫ LiteralKernelNegation318.negation N := by
  rw [ThreeTorsionDiamond318.diamond_neg_one]
  exact finite_compatibility N
end LiteralKernelDiamond318
