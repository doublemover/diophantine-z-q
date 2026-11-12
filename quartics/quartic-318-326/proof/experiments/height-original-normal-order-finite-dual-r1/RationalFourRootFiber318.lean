module
public import FourRootOrderSigns318
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public section
noncomputable section
namespace RationalFourRootFiber318
open FourRootOrder318 FourRootOrderSigns318
set_option maxHeartbeats 500000
attribute [-instance] DivisionRing.toRatAlgebra
variable (a : Fin 4 → ℚ)

local instance fiberFinite : Module.Finite ℚ (Order a) := (finite_free a).1
local instance fiberNontrivial : Nontrivial (Order a) :=
  Module.nontrivial_of_finrank_pos (R := ℚ) (by rw [rank_sixteen]; decide)

/-- A maximal ideal of the actual rank-sixteen rational fiber algebra.
No irreducibility or independence of the specialized squareclasses is assumed. -/
@[expose] def chosenIdeal : Ideal (Order a) :=
  (Ideal.exists_le_maximal (⊥ : Ideal (Order a)) bot_ne_top).choose

instance chosenIdeal_maximal : (chosenIdeal a).IsMaximal :=
  (Ideal.exists_le_maximal (⊥ : Ideal (Order a)) bot_ne_top).choose_spec.1

abbrev PointField := Order a ⧸ chosenIdeal a
instance pointField : Field (PointField a) := Ideal.Quotient.field _
instance pointField_finite : Module.Finite ℚ (PointField a) := inferInstance
instance pointField_numberField : NumberField (PointField a) :=
  NumberField.of_module_finite ℚ (PointField a)

/-- The quotient map is an actual rational point of the four-root fiber. -/
@[expose] def point : Order a →ₐ[ℚ] PointField a := Ideal.Quotient.mkₐ ℚ _

theorem point_surjective : Function.Surjective (point a) := Ideal.Quotient.mk_surjective

/-- Specialization can decrease the degree; it need not preserve generic degree sixteen. -/
theorem field_degree_le : Module.finrank ℚ (PointField a) ≤ 16 := by
  calc
    Module.finrank ℚ (PointField a) ≤ Module.finrank ℚ (Order a) :=
      LinearMap.finrank_le_finrank_of_surjective (f := (point a).toLinearMap) (point_surjective a)
    _ = 16 := rank_sixteen a

@[expose] def root (i : Fin 4) : PointField a := point a (generator a i)

theorem root_square (i : Fin 4) : (root a i)^2 = algebraMap ℚ (PointField a) (a i) := by
  rw [root, ← map_pow, generator_square, AlgHom.commutes]

theorem root_ne_zero (i : Fin 4) (ha : a i ≠ 0) : root a i ≠ 0 := by
  intro h
  have hs := root_square a i
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
  exact ha ((algebraMap ℚ (PointField a)).injective (hs.symm.trans (map_zero _).symm))

end RationalFourRootFiber318
