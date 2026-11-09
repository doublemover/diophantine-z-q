module
public import IntegralInfinityChart318
public import InfinityParameters318
public section
noncomputable section
namespace IntegralInfinityCoefficients318
open Polynomial IntegralInfinityChart318
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def c0 : Order R c := algebraMap R (Order R c) (c 0 : R)
@[expose] def k0 : Order R c := algebraMap R (Order R c) (↑(c 0)⁻¹ : R)
@[expose] def otherTwists : Order R c :=
  algebraMap R (Order R c) (∏ j : Fin 3, (c j.succ : R))
@[expose] def coefficient0 : Order R c :=
  4 * otherTwists R c * k0 R c ^ 5 * coordinate R c ^ 2 * inverseDenominator R c
@[expose] def coefficient1 : Order R c :=
  4 * otherTwists R c * k0 R c ^ 4 * inverseDenominator R c

theorem c0_k0 : c0 R c * k0 R c = 1 := by
  rw [c0,k0,←map_mul,Units.mul_inv,map_one]

theorem coefficient0_relation : coefficient0 R c =
    k0 R c * coordinate R c ^ 2 * coefficient1 R c := by
  simp only [coefficient0,coefficient1]
  ring

theorem denominator_shape : orderDenominator R c =
    ∏ j : Fin 3, algebraMap R (Order R c) (c j.succ : R) * k0 R c *
      (1 - algebraMap R (Order R c) (contact R j) * k0 R c * coordinate R c ^ 2) := by
  have hC (a : R) : algebraMap R[X] (Order R c) (C a) = algebraMap R (Order R c) a :=
    (IsScalarTower.algebraMap_apply R R[X] (Order R c) a).symm
  simp only [orderDenominator,denominator,coefficient,map_prod,map_mul,map_sub,
    map_one,map_pow,hC,k0,coordinate,←IsScalarTower.algebraMap_apply]

theorem coefficient1_unit (h2 : IsUnit (2 : R)) : IsUnit (coefficient1 R c) := by
  have h4 : IsUnit (4 : Order R c) := by
    have h4R : IsUnit (4 : R) := by
      simpa only [show (2 : R)^2 = (4 : R) by ring] using h2.pow 2
    simpa only [map_ofNat] using h4R.map (algebraMap R (Order R c))
  have hC : IsUnit (otherTwists R c) :=
    (IsUnit.prod_univ_iff.mpr (fun j => (c j.succ).isUnit)).map (algebraMap R (Order R c))
  have hk : IsUnit (k0 R c) := ((c 0)⁻¹).isUnit.map (algebraMap R (Order R c))
  have hd : IsUnit (inverseDenominator R c) :=
    isUnit_iff_exists_inv.mpr ⟨orderDenominator R c,by rw [mul_comm,denominator_inverse]⟩
  exact ((h4.mul hC).mul (hk.pow 4)).mul hd

/-- The integral coefficients specialize to exactly the original rational
reciprocal radicands. No factor involving a contact is inverted integrally. -/
theorem rational_coefficient (c : Fin 4 → ℚˣ) (j : Fin 3) :
    coefficient ℚ c j = InfinityParameters318.coefficient c j := by
  rw [InfinityParameters318.coefficient_shape]
  have ha : contact ℚ j = InfinityParameters318.contact j := by
    fin_cases j <;> rfl
  simp only [coefficient,ha,div_eq_mul_inv,Units.val_inv_eq_inv_val]

theorem rational_denominator (c : Fin 4 → ℚˣ) :
    denominator ℚ c = ∏ j : Fin 3, InfinityParameters318.coefficient c j := by
  simp only [denominator,rational_coefficient]

end IntegralInfinityCoefficients318
