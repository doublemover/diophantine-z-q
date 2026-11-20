module
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
public section

namespace OriginalRRC45FiniteSmithCenter318
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The finite center read of one surviving first coordinate. The carrier
indices are the same on every retained residue. No invertibility or
nonzero hypothesis is made on gamma, which includes the paired factor. -/
structure FiniteRead (R : Type*) [CommRing R] (I J : Type*) [Fintype I] [Fintype J]
    (a : ℕ) (target : R) where
  d : J → I → R
  z : J → R
  v : I → R
  q : J → R
  gamma : R
  closed : ∀ i, ∑ j, q j * d j i = 0
  marked : ∀ j, (a:R) * z j = ∑ i, d j i * v i
  read : target = gamma * ∑ j, q j * z j

/-- The actual selected row kills the marked boundary over the SAME
finite coefficient ring. No division by the positive annihilator. -/
theorem FiniteRead.mul_target_eq_zero {R : Type*} [CommRing R] {a : ℕ} {target : R}
    (F : FiniteRead R I J a target) : (a:R) * target = 0 := by
  have h : (a:R) * (∑ j, F.q j * F.z j) = 0 := by
    calc
      _ = ∑ j, F.q j * ((a:R) * F.z j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, ∑ i, (F.q j * F.d j i) * F.v i := by
        simp only [F.marked,Finset.mul_sum,mul_assoc]
      _ = ∑ i, (∑ j, F.q j * F.d j i) * F.v i := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = 0 := by simp only [F.closed,zero_mul,Finset.sum_const_zero]
  rw [F.read,←mul_assoc,mul_comm (a:R) F.gamma,mul_assoc,h,mul_zero]

/-- Any retained integral survivor row really gives the finite
annihilator condition after coefficient reduction. -/
theorem reduce_closed (k : ℕ) (q : J → ℤ_[2]) (d : J → I → ℤ_[2])
    (hq : ∀ i, ∑ j, q j * d j i = 0) (i : I) :
    (∑ j, PadicInt.toZModPow k (q j) * PadicInt.toZModPow k (d j i)) = 0 := by
  have h := congrArg (fun x : ℤ_[2] => PadicInt.toZModPow k x) (hq i)
  simpa only [map_sum,map_mul,map_zero] using h

/-- All reductions are detected even from cofinally many witnesses at
unrelated finite stages. A fixed ring element is reduced, not an
arbitrary family of unmatched scalars. -/
theorem padic_zero_of_cofinal (x : ℤ_[2])
    (h : ∀ r : ℕ, ∃ k : ℕ, r ≤ k ∧ PadicInt.toZModPow k x = 0) :
    x = 0 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  obtain ⟨k,hkr,hx⟩ := h r
  let f := ZMod.castHom (pow_dvd_pow 2 hkr) (ZMod (2^r))
  calc
    PadicInt.toZModPow r x = f (PadicInt.toZModPow k x) :=
      (DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow r k hkr) x).symm
    _ = PadicInt.toZModPow r 0 := by simp only [hx,map_zero]

/-- Same actual scaled base read, with an optional fixed extra clearing
power s. Only the fixed integer a is inverted logically, AFTER p-adic
separation and in the integral domain (never at finite level). -/
theorem lift_zero_of_cofinal_reads (base : ℤ_[2]) (a s : ℕ) (ha : 0 < a)
    (rows : ∀ r : ℕ, ∃ k : ℕ, r ≤ k ∧
      Nonempty (FiniteRead (ZMod (2^k)) I J a
        (PadicInt.toZModPow k ((2:ℤ_[2])^s * base)))) :
    base = 0 := by
  have hzero : (a:ℤ_[2]) * ((2:ℤ_[2])^s * base) = 0 := by
    apply padic_zero_of_cofinal
    intro r
    obtain ⟨k,hkr,⟨row⟩⟩ := rows r
    refine ⟨k,hkr,?_⟩
    rw [map_mul,map_natCast]
    exact row.mul_target_eq_zero
  have ha' : (a:ℤ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have htwo : (2:ℤ_[2])^s ≠ 0 := pow_ne_zero _ (two_ne_zero : (2:ℤ_[2]) ≠ 0)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha')).resolve_left htwo

end OriginalRRC45FiniteSmithCenter318

#print axioms OriginalRRC45FiniteSmithCenter318.FiniteRead.mul_target_eq_zero
#print axioms OriginalRRC45FiniteSmithCenter318.lift_zero_of_cofinal_reads
