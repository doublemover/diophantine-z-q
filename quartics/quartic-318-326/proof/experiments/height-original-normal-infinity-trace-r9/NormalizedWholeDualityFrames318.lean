module
public import FourRootDualityUnitScale318
public import FiniteDualModuleAction318
public import NormalizedWholeOverlap318
public section
noncomputable section
namespace NormalizedWholeDualityFrames318
open Polynomial NormalizedReciprocalLaurent318 NormalizedWholeOverlap318
open FourRootIntegralDuality318
set_option maxHeartbeats 1800000
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

/-- The actual finite dual of the ENTIRE finite polynomial chart in the
already constructed proper model, with its multiplication module action. -/
abbrev FiniteDual := FiniteDualModuleAction318.Dual R[X] (FiniteOrder R d a)
abbrev InfinityDual := FiniteDualModuleAction318.Dual R[X] (InfinityOrder R d a)

@[expose] def finiteFrame : FiniteOrder R d a ≃ₗ[FiniteOrder R d a] FiniteDual R d a :=
  FiniteDualModuleAction318.frame R[X] (FiniteOrder R d a)
    (frame (DVRNormalizedFiniteOrder318.coefficient R d a))
@[expose] def infinityFrame : InfinityOrder R d a ≃ₗ[InfinityOrder R d a] InfinityDual R d a :=
  FiniteDualModuleAction318.frame R[X] (InfinityOrder R d a)
    (frame (DVRNormalizedInfinityOrder318.coefficient R d a))

/-- The exact dual-functional transition on the existing WHOLE Laurent
intersection. This is an identity of actual linear maps, not a pointwise
identity only at the distinguished arithmetic section. -/
theorem overlap_coefficient :
    (coefficient (infinityParameter R d a)).comp (fullOverlap R d a).toLinearMap =
      (coordinate R:Laurent R)^4 • coefficient (finiteParameter R d a) :=
  FourRootDualityUnitScale318.coefficient_linearMap _ _ _ (parameter_identity R d a)

theorem overlap_inverse (x : FourRootOrder318.Order (finiteParameter R d a)) :
    coefficient (finiteParameter R d a) x=(↑(coordinate R)⁻¹:Laurent R)^4*
      coefficient (infinityParameter R d a) (fullOverlap R d a x) :=
  FourRootDualityUnitScale318.coefficient_inverse _ _ _ (parameter_identity R d a) x

/-- Multiplying by the genuine base-coordinate differential change
 dt=-t² ds changes the order-dual factor t^-4 to -t^-2. This algebraic
identity records the precise transition required for the relative
canonical comparison; it does not assert that comparison as a premise. -/
theorem relative_canonical_transition_scalar :
    (↑(coordinate R)⁻¹:Laurent R)^4 * (-(coordinate R:Laurent R)^2)=
      -(↑(coordinate R)⁻¹:Laurent R)^2 := by
  have h : (↑(coordinate R)⁻¹:Laurent R)*(coordinate R:Laurent R)=1 := Units.inv_mul _
  calc
    _ = -((↑(coordinate R)⁻¹:Laurent R)^2*
        ((↑(coordinate R)⁻¹:Laurent R)*(coordinate R:Laurent R))^2) := by ring
    _ = _ := by rw [h,one_pow,mul_one]
end NormalizedWholeDualityFrames318
