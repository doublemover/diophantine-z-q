module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic
public section
noncomputable section
namespace DVRInertiaCharacterParity318
open IsDiscreteValuationRing IsLocalRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A tame inertia automorphism fixing the actual residue field and negating
an actual uniformizer acts on the leading coefficient by the order parity. -/
theorem order_sign (σ : R ≃+* R) (hres : ∀ a : R, residue R (σ a) = residue R a)
    (π : R) (hπ : Irreducible π) (hσπ : σ π = -π)
    (x : R) (hx : x ≠ 0) (b : Bool) (hσx : σ x = (if b then -1 else 1) * x) :
    (-1 : ResidueField R) ^ (addVal R x).toNat = if b then -1 else 1 := by
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  have hv : addVal R x = n := addVal_def x u hπ n hu
  have he : σ (u : R) * (-1 : R) ^ n = (if b then -1 else 1) * (u : R) := by
    apply mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero)
    calc
      _ = σ ((u : R) * π ^ n) := by
        rw [map_mul, map_pow, hσπ, ← neg_one_mul π, mul_pow]
        ring
      _ = (if b then -1 else 1) * ((u : R) * π ^ n) := by
        rw [← hu, hσx]
      _ = _ := by ring
  have hr := congrArg (residue R) he
  simp only [map_mul, map_pow, map_neg, map_one, hres] at hr
  have hur : residue R (u : R) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr u.isUnit
  rw [hv, ENat.toNat_natCast]
  apply mul_left_cancel₀ hur
  cases b <;> simpa only [Bool.false_eq_true, ite_false, ite_true, map_neg, map_one,
    mul_comm] using hr

variable [CharZero (ResidueField R)]
/-- The genuine local inertia sign determines even versus odd order at the
actual closed point. Its residue field need not equal the rational base. -/
theorem order_even_iff (σ : R ≃+* R) (hres : ∀ a : R, residue R (σ a) = residue R a)
    (π : R) (hπ : Irreducible π) (hσπ : σ π = -π)
    (x : R) (hx : x ≠ 0) (b : Bool) (hσx : σ x = (if b then -1 else 1) * x) :
    Even (addVal R x).toNat ↔ b = false := by
  rw [← neg_one_pow_eq_one_iff_even (R := ResidueField R) (by norm_num),
    order_sign σ hres π hπ hσπ x hx b hσx]
  cases b <;> norm_num
end DVRInertiaCharacterParity318
