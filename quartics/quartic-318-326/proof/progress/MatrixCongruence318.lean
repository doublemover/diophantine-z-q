module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic
public section
namespace MatrixCongruence318
set_option maxHeartbeats 0
noncomputable section

/-- First-order binomial expansion in a possibly noncommutative ring. -/
theorem one_add_pow_remainder {R:Type*} [Ring R] (x:R) (m:ℕ) :
    ∃z:R,(1+x)^m=1+m • x+x^2*z := by
  induction m with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨z,hz⟩:=ih
    refine ⟨z+m • (1:R)+z*x,?_⟩
    rw [pow_succ,hz,add_nsmul,one_nsmul]
    simp only [mul_add,add_mul,one_mul,mul_one,mul_smul_comm,smul_mul_assoc]
    noncomm_ring

variable {n:Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℤ

/-- Entrywise divisibility is exactly an integral scalar matrix factor. -/
theorem exists_smul_iff (d:ℤ) (A:M) :
    (∃B:M,A=d • B) ↔ ∀i j,d∣A i j := by
  constructor
  · rintro ⟨B,rfl⟩ i j
    exact ⟨B i j,rfl⟩
  · intro h
    choose B hB using h
    exact ⟨B,by ext i j; exact hB i j⟩

/-- The first-order expansion after cancelling the common integral scalar. -/
theorem torsion_equation (A B:M) (d:ℤ) (hd:d≠0) (q:ℕ)
    (hA:A=1+d • B) (hpow:A^q=1) :
    ∃C:M,(q:ℤ) • B+d • (B^2*C)=0 := by
  obtain ⟨C,hC⟩:=one_add_pow_remainder (d • B) q
  rw [←hA,hpow] at hC
  have he:d • ((q:ℤ) • B+d • (B^2*C))=0 := by
    have ht:(q:ℤ) • (d • B)+(d • B)^2*C=0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ]
      exact add_eq_left.mp (by simpa only [add_assoc] using hC.symm)
    rw [smul_add,smul_smul,smul_smul]
    rw [smul_pow,smul_mul_assoc] at ht
    simpa only [pow_two,smul_smul,mul_comm d (q:ℤ)] using ht
  exact ⟨C,(smul_eq_zero_iff_right hd).mp he⟩

/-- A torsion relation of order prime to three improves a nontrivial
three-adic congruence by one step. -/
theorem lift_coprime (A B:M) (d:ℤ) (hd:d≠0) (hd3:3∣d) (q:ℕ)
    (hq:¬(3:ℤ)∣(q:ℤ)) (hA:A=1+d • B) (hpow:A^q=1) :
    ∃C:M,B=3 • C := by
  obtain ⟨C,hC⟩:=torsion_equation A B d hd q hA hpow
  apply (exists_smul_iff 3 B).mpr
  intro i j
  have he:=congrArg (fun X:M=>X i j) hC
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply] at he
  have hv:(3:ℤ)∣(q:ℤ)*B i j := by
    rw [show (q:ℤ)*B i j= -(d*(B^2*C) i j) by linarith only [he]]
    exact dvd_neg.mpr (dvd_mul_of_dvd_left hd3 _)
  exact (Int.prime_three.dvd_mul.mp hv).resolve_left hq

/-- The exceptional order-three equation has one extra factor of three,
which still leaves a divisible remainder after cancellation. -/
theorem cube_expansion (d:ℤ) (B:M) :
    (1+(3*d) • B)^3=1+(9*d) • (B+3 • (d • B^2+d^2 • B^3)) := by
  have hc (x:M) : (1+x)^3=1+3 • x+3 • x^2+x^3 := by
    simp only [show (3:ℕ)=2+1 from rfl,add_nsmul,one_nsmul,two_nsmul]
    noncomm_ring
  rw [hc]
  simp only [smul_pow,smul_add,smul_smul]
  module

 theorem lift_three (A B:M) (d:ℤ) (hd:d≠0)
    (hA:A=1+(3*d) • B) (hpow:A^3=1) : ∃C:M,B=3 • C := by
  have he:=cube_expansion d B
  rw [←hA,hpow] at he
  have hh:(9*d) • (B+3 • (d • B^2+d^2 • B^3))=0 :=
    add_eq_left.mp he.symm
  have hh':B+3 • (d • B^2+d^2 • B^3)=0 :=
    (smul_eq_zero_iff_right (mul_ne_zero (by norm_num) hd)).mp hh
  refine ⟨-(d • B^2+d^2 • B^3),?_⟩
  rw [smul_neg]
  exact eq_neg_of_add_eq_zero_left hh'

end
end MatrixCongruence318
