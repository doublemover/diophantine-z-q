module
public import QuarticOptimization
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.Minpoly.Finite
public section
namespace G4Nonvanishing
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] noncomputable def H : ℤ[X] := X^4 + C (-1326) * X^3 + C (-1465230) * X^2 + C (-2615435550) * X^1 + C (-5610109254750) * X^0

theorem degree_H : H.natDegree=4 := by
  unfold H
  compute_degree <;> norm_num

theorem monic_H : H.Monic := by
  unfold H
  monicity!

theorem eisenstein_H : H.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
  refine ⟨?_,?_,?_⟩
  · rw [monic_H.leadingCoeff,Ideal.mem_span_singleton]
    norm_num
  · intro n hn
    rw [degree_H] at hn
    interval_cases n <;> norm_num [H,Ideal.mem_span_singleton,Polynomial.coeff_add,
      Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    norm_num [H,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]

theorem irreducible_H : Irreducible H := by
  apply eisenstein_H.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num : (2:ℤ) ≠ 0)).mpr (by norm_num)
  · exact monic_H.isPrimitive
  · rw [degree_H]; norm_num

@[expose] noncomputable def HQ : ℚ[X] := H.map (Int.castRingHom ℚ)

theorem irreducible_HQ : Irreducible HQ :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic_H.isPrimitive).mp irreducible_H

theorem degree_HQ : HQ.natDegree=4 := by
  rw [HQ,monic_H.natDegree_map,degree_H]

theorem monic_HQ : HQ.Monic := monic_H.map _

theorem HQ_no_root {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 4) (x : K) :
    aeval x HQ ≠ 0 := by
  intro hx
  have heq := minpoly.eq_of_irreducible_of_monic irreducible_HQ hx monic_HQ
  have hdeg := minpoly.natDegree_le (A := ℚ) x
  rw [←heq,degree_HQ] at hdeg
  omega

@[expose] def G4 {K : Type*} [Field K] (x : K) : K := (1/1)*x^0 + (-2/5)*x^1 + (-2/15)*x^2 + (-14/195)*x^3 + (-154/3315)*x^4

theorem scaled_reverse_identity {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (x : K) (hx : x ≠ 0) :
    (aeval ((3315:K)/x) HQ)*x^4=(3315:K)^4*G4 x := by
  simp only [HQ,H,Polynomial.aeval_def,Polynomial.eval₂_map,Polynomial.eval₂_add,
    Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C]
  norm_num [G4]
  field_simp
  <;> ring

theorem G4_nonzero {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 4) (x : K) :
    G4 x ≠ 0 := by
  intro hg
  have hx : x ≠ 0 := by intro hx; simp [hx,G4] at hg
  have hh := scaled_reverse_identity x hx
  rw [hg,mul_zero] at hh
  have he : aeval ((3315:K)/x) HQ=0 :=
    (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 4 hx)
  exact HQ_no_root hdim _ he

end G4Nonvanishing
