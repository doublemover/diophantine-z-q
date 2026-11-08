module
public import LiteralComplementNeighborhood318
public import InfinityKernelNeighborhoodTripling318
public section
noncomputable section
namespace LiteralKernelComplementZero318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N

lemma origin_unit : IsUnit (InfinityChart318.origin A B
    (InfinityKernelNeighborhoodAlgebra318.denominator A B)) := by
  rw [InfinityKernelNeighborhoodOrigin318.origin_denominator]
  exact (OpenJModel318.base_units N).2.1

/-- The complementary component of the actual literal tripling kernel is
exactly the actual zero section, including all infinitesimal directions. -/
theorem complement_zero : LiteralComplementNeighborhood318.point N=
    LiteralKernelZeroSection318.complementStructure N ≫ WeierstrassGluing318.infinity A B := by
  apply LiteralComplementNeighborhood318.complement_zero_of_neighborhood N
    (InfinityKernelNeighborhoodAlgebra318.denominator A B) (origin_unit N)
  intro X x hx
  have h:=InfinityKernelNeighborhoodZero318.scheme_zero A B hD x hx
  exact h

/-- Actual inverse maps between the entire complementary kernel scheme and
its original base, with no remaining neighborhood hypothesis. -/
@[expose] def iso : LiteralKernelComplement318.complement N ≅
    Spec (CommRingCat.of (OpenJModel318.Base N)) :=
  LiteralKernelZeroSection318.complementIsoOfZero N (complement_zero N)
@[reassoc] theorem iso_hom : (iso N).hom=LiteralKernelZeroSection318.complementStructure N := rfl
@[reassoc] theorem iso_inv : (iso N).inv=LiteralKernelZeroSection318.intoComplement N := rfl
end LiteralKernelComplementZero318
