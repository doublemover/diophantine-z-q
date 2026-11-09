module
public import IntegralInfinityCoefficients318
public import InfinityDenominatorOverlap318
public import ReciprocalBicanonicalIdentity318
public import VerticalCotangentSections318
public section
noncomputable section
namespace IntegralInfinityGenericIdentity318
open IntegralInfinityChart318 IntegralInfinityCoefficients318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
  (K : Type*) [Field K] [Algebra (Order R c) K] [Algebra R K] [IsScalarTower R (Order R c) K]
@[expose] def u : K := algebraMap (Order R c) K (coordinate R c)
@[expose] def t : K := algebraMap R K (c 0 : R) / u R c K ^ 2

theorem reciprocal_relation (hu : u R c K ≠ 0) :
    u R c K ^ 2 * t R c K = algebraMap R K (c 0 : R) := by
  unfold t
  field_simp [hu]

theorem quartic_shape : VerticalSection318.denominator (t R c K) =
    t R c K * ∏ j : Fin 3, (t R c K - algebraMap R K (contact R j)) := by
  simp [VerticalSection318.denominator,VerticalSection318.contacts,contact,Fin.prod_univ_succ,map_ofNat]
  <;> ring

theorem denominator_identity (hu : u R c K ≠ 0) :
    algebraMap R K (c 0 : R)^7 * algebraMap (Order R c) K (orderDenominator R c) =
      algebraMap (Order R c) K (otherTwists R c) * u R c K ^ 8 *
        VerticalSection318.denominator (t R c K) := by
  rw [denominator_shape,quartic_shape]
  simp only [map_prod,map_mul,map_sub,map_pow,map_one,k0,otherTwists,
    ←IsScalarTower.algebraMap_apply,u]
  apply InfinityDenominatorOverlap318.cleared_product
  · rw [←map_mul,Units.mul_inv,map_one]
  · exact reciprocal_relation R c K hu

theorem quartic_ne_zero (hu : u R c K ≠ 0) :
    VerticalSection318.denominator (t R c K) ≠ 0 := by
  have hd := congrArg (algebraMap (Order R c) K) (denominator_inverse R c)
  rw [map_mul,map_one] at hd
  have hd0 : algebraMap (Order R c) K (orderDenominator R c) ≠ 0 := by
    intro h;rw [h,zero_mul] at hd;exact zero_ne_one hd
  have hc : algebraMap R K (c 0 : R) ≠ 0 := ((c 0).isUnit.map (algebraMap R K)).ne_zero
  intro hp
  have he := denominator_identity R c K hu
  rw [hp,mul_zero] at he
  exact (mul_ne_zero (pow_ne_zero 7 hc) hd0) he

/-- Exact twist powers and the original reciprocal-coordinate derivative survive. -/
theorem coefficient_cleared (hu : u R c K ≠ 0) :
    VerticalSection318.denominator (t R c K) * algebraMap (Order R c) K (coefficient0 R c) =
      (-(2 * (u R c K)⁻¹ * t R c K))^2 := by
  have hk := congrArg (algebraMap (Order R c) K) (c0_k0 R c)
  simp only [map_mul,map_one,c0,←IsScalarTower.algebraMap_apply] at hk
  have hd := congrArg (algebraMap (Order R c) K) (denominator_inverse R c)
  rw [map_mul,map_one] at hd
  have h1 := ReciprocalBicanonicalIdentity318.cleared _ _ _ _ _ _ _ hk hd
    (denominator_identity R c K hu)
  have h2 := ReciprocalBicanonicalIdentity318.factor_cleared
    (u R c K) (u R c K)⁻¹ (t R c K) (algebraMap R K (c 0 : R))
    (mul_inv_cancel₀ hu) (reciprocal_relation R c K hu)
  apply mul_left_cancel₀ (pow_ne_zero 6 hu)
  simpa only [coefficient0,map_mul,map_pow,map_ofNat,u] using h1.trans h2.symm

theorem coefficient1_relation (hu : u R c K ≠ 0) :
    t R c K * algebraMap (Order R c) K (coefficient0 R c) =
      algebraMap (Order R c) K (coefficient1 R c) := by
  have hk := congrArg (algebraMap (Order R c) K) (c0_k0 R c)
  simp only [map_mul,map_one,c0,←IsScalarTower.algebraMap_apply] at hk
  simpa only [coefficient0,coefficient1,map_mul,map_pow,map_ofNat,u] using
    ReciprocalBicanonicalIdentity318.q1_relation _ _ _ _ _ _ hk (reciprocal_relation R c K hu)

end IntegralInfinityGenericIdentity318
