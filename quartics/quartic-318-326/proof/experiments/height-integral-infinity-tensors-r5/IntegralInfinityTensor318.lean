module
public import IntegralInfinityGenericIdentity318
public import ReciprocalCoordinateDifferential318
public import Mathlib.RingTheory.Flat.Localization
public section
noncomputable section
namespace IntegralInfinityTensor318
open Polynomial IntegralInfinityChart318 IntegralInfinityCoefficients318
open IntegralInfinityGenericIdentity318 IntegralCotangentTensor318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (h2 : IsUnit (2 : R))
@[expose] def tensor0 : KaehlerDifferential R (Order R c) ⊗[Order R c] KaehlerDifferential R (Order R c) :=
  (squareFrame (frame R c h2)).symm ((VerticalSection318.J : Order R c)^2 * coefficient0 R c)
@[expose] def tensor1 : KaehlerDifferential R (Order R c) ⊗[Order R c] KaehlerDifferential R (Order R c) :=
  (squareFrame (frame R c h2)).symm ((VerticalSection318.J : Order R c)^2 * coefficient1 R c)

variable [IsDomain R] [IsDomain (Order R c)]
  (K : Type*) [Field K] [Algebra (Order R c) K] [Algebra R K]
  [IsScalarTower R (Order R c) K] [IsFractionRing (Order R c) K]

include h2

theorem coordinate_ne_zero : coordinate R c ≠ 0 := by
  letI : Module.Free (Base R c) (Order R c) := (finite_free_etale R c h2).2.1
  letI : Module.Flat R[X] (Order R c) := Module.Flat.trans R[X] (Base R c) (Order R c)
  simpa only [coordinate,←IsScalarTower.algebraMap_apply,map_zero] using
    (FaithfulSMul.algebraMap_injective R[X] (Order R c)).ne (Polynomial.X_ne_zero (R := R))

theorem u_ne_zero : u R c K ≠ 0 := by
  simpa only [u,map_zero] using (IsFractionRing.injective (Order R c) K).ne
    (coordinate_ne_zero R c h2)

theorem derived_t : FractionSourceSections318.derived (frame R c h2) (t R c K) =
    -(2 * (u R c K)⁻¹ * t R c K) := by
  have hdu : FractionKaehlerFrame318.genericFrame (K := K) (frame R c h2)
      (KaehlerDifferential.D R K (u R c K)) = 1 := by
    rw [u,←KaehlerDifferential.map_D R R (Order R c) K,
      FractionKaehlerFrame318.genericFrame_map,frame_D,map_one]
  have hd := ReciprocalCoordinateDifferential318.D_of_inverse
    (t R c K) (u R c K) (u R c K)⁻¹ (c 0 : R)
    (mul_inv_cancel₀ (u_ne_zero R c h2 K)) (reciprocal_relation R c K (u_ne_zero R c h2 K))
  have he : FractionKaehlerFrame318.genericFrame (K := K) (frame R c h2)
      (KaehlerDifferential.D R K (t R c K)) =
      FractionSourceSections318.derived (frame R c h2) (t R c K) :=
    Derivation.liftKaehlerDifferential_comp_D _ _
  rw [←he,hd,map_smul,hdu,smul_eq_mul,mul_one]

theorem coefficient0_image :
    algebraMap (Order R c) K ((VerticalSection318.J : Order R c)^2 * coefficient0 R c) =
      VerticalSection318.section0 (FractionSourceSections318.derived (frame R c h2)) (t R c K) := by
  rw [VerticalSection318.section0,derived_t]
  apply (eq_div_iff (quartic_ne_zero R c K (u_ne_zero R c h2 K))).mpr
  rw [map_mul,map_pow,map_intCast]
  calc
    (VerticalSection318.J : K)^2 * algebraMap (Order R c) K (coefficient0 R c) *
        VerticalSection318.denominator (t R c K) =
      (VerticalSection318.J : K)^2 * (VerticalSection318.denominator (t R c K) *
        algebraMap (Order R c) K (coefficient0 R c)) := by ring
    _ = _ := by rw [coefficient_cleared R c K (u_ne_zero R c h2 K)]

theorem coefficient1_image :
    algebraMap (Order R c) K ((VerticalSection318.J : Order R c)^2 * coefficient1 R c) =
      VerticalSection318.section1 (FractionSourceSections318.derived (frame R c h2)) (t R c K) := by
  rw [VerticalSection318.section1,←coefficient0_image R c h2 K]
  simp only [map_mul,map_pow,map_intCast]
  rw [←coefficient1_relation R c K (u_ne_zero R c h2 K)]
  ring

/-- Actual whole-infinity integral tensors realize the original generic pair
with the exact t=c0/u^2 convention and powers c0^-5 and c0^-4. -/
theorem tensor_images :
    IntegralCotangentTensor318.map (frame R c h2) (tensor0 R c h2) =
      VerticalCotangentSections318.q0 (R := R) (t R c K) ∧
    IntegralCotangentTensor318.map (frame R c h2) (tensor1 R c h2) =
      VerticalCotangentSections318.q1 (R := R) (t R c K) := by
  constructor
  · apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) (frame R c h2))).injective
    rw [frame_map,tensor0,LinearEquiv.apply_symm_apply,VerticalCotangentSections318.q0_coefficient]
    exact coefficient0_image R c h2 K
  · apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) (frame R c h2))).injective
    rw [frame_map,tensor1,LinearEquiv.apply_symm_apply,VerticalCotangentSections318.q1_coefficient]
    exact coefficient1_image R c h2 K

end IntegralInfinityTensor318
