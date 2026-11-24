module
public import OriginalUniformSparseClassifying318
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Coprime.Basic

/-! A literal relative Bézout certificate for the sparse genus-two affine
chart. This proves the polynomial nonsingularity input to the relative
double-cover construction; it does not assume a native discriminant API. -/

public section
namespace OriginalUniformSparseSmoothChart318

section Algebraic
variable {R : Type*} [CommRing R]

@[expose] def eqVal (s t x : R) : R :=
  t^2*(5-s*t)^3 + (-2*(s*t)*t*(5-s*t)^2)*x +
  (-10*(s*t)*(s*t-5))*x^3 + (-2*(s*t)*s)*x^5 + s^2*x^6

@[expose] def derVal (s t x : R) : R :=
  -2*(s*t)*t*(5-s*t)^2 + 3*(-10*(s*t)*(s*t-5))*x^2 +
  5*(-2*(s*t)*s)*x^4 + 6*s^2*x^5

@[expose] def collision (s t : R) : R :=
  (s+t)*(s*t)^2 - 5*(s+t)*(s*t)+10*(s*t)^2-90*(s*t)+216

@[expose] def delta (s t : R) : R :=
  -10*collision s t*t^3*(s*t-5)^4

@[expose] def v (s t x : R) : R :=
  let N := s*t
  let W := N-5
  (5*s^2*t+11*N-25*s-39)*t^2*W^2 -
  2*t*(s*t^2+12*N-81)*W^2*x +
  N*W*(3*s*t^2+33*N+17*t-165)*x^2 -
  5*N*(N-9)*W*x^3 +
  2*s*(4*N^2+4*s*t^2-29*N+45)*x^4 -
  (3*N+4*t-15)*s^2*x^5

@[expose] def u (s t x : R) : R :=
  let N := s*t
  let W := N-5
  2*t*(5*s*t^2+39*N-216)*W^2 -
  4*N*W*(4*s*t^2+27*N-135)*x +
  26*N*(N-9)*W*x^2 -
  2*s*(21*N^2+20*s*t^2-159*N+270)*x^3 +
  6*(3*N+4*t-15)*s^2*x^4

theorem bezout (s t x : R) :
    u s t x*eqVal s t x+v s t x*derVal s t x = delta s t := by
  unfold u eqVal v derVal delta collision
  dsimp only
  ring

open Polynomial

/-- Actual polynomial of the affine equation, not a presupposed residue class. -/
noncomputable def equation (s t : R) : Polynomial R :=
  eqVal (C s) (C t) X

theorem derivative_equation (s t : R) :
    derivative (equation s t) = derVal (C s) (C t) X := by
  unfold equation eqVal derVal
  simp [derivative_add, derivative_mul, derivative_pow, C_ofNat]
  ring

lemma delta_cast (s t : R) : delta (C s) (C t) = C (delta s t) := by
  unfold delta collision
  simp only [map_mul,map_pow,map_sub,map_add,map_neg,map_ofNat]

/-- Gives relative coprimality under a unit on the chosen base, so the
same affine chart remains nonsingular after arbitrary specialization. -/
theorem relative_coprime (s t : R) (unit : IsUnit (delta s t)) :
    IsCoprime (equation s t) (derivative (equation s t)) := by
  rcases unit with ⟨q,hq⟩
  have hb := bezout (C s) (C t) X
  rw [← equation, ← derivative_equation, delta_cast, ← hq] at hb
  refine ⟨C (↑q⁻¹ : R) * u (C s) (C t) X, C (↑q⁻¹ : R) * v (C s) (C t) X, ?_⟩
  calc
    _ = C (↑q⁻¹ : R) * (u (C s) (C t) X * equation s t +
      v (C s) (C t) X * derivative (equation s t)) := by ring
    _ = 1 := by rw [hb, ← map_mul, Units.inv_mul, map_one]
end Algebraic

section Ordinary
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem actual_sparse_value (s t x : K) : eqVal s t x =
    OriginalUniformSparseIgusa318.sparse s t 0 +
    OriginalUniformSparseIgusa318.sparse s t 1*x +
    OriginalUniformSparseIgusa318.sparse s t 3*x^3 +
    OriginalUniformSparseIgusa318.sparse s t 5*x^5 +
    OriginalUniformSparseIgusa318.sparse s t 6*x^6 := rfl

/-- Nonzero actual Igusa discriminant from the classifying proof supplies the
unit in the explicit affine Bézout identity. -/
theorem unit_of_igusa (s t : K) (hi : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    IsUnit (delta s t) := by
  have h := (OriginalUniformSparseIgusa318.reads_factored s t).2.2.2
  change OriginalUniformSparseIgusa318.i10 s t =
    200000*(collision s t)^2*(s*t)^10*(s*t-5)^10 at h
  have hs := hi
  rw [h] at hs
  have hw := (mul_ne_zero_iff.mp hs).2
  have hN := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs).1).2
  have hC := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs).1).1).2
  have ht : t ≠ 0 := by
    intro ht
    rw [ht,mul_zero,zero_pow (by decide : 10 ≠ 0)] at hN
    exact hN rfl
  have hW : s*t-5 ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : 10 ≠ 0)] at hw
    exact hw rfl
  have hC0 : collision s t ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : 2 ≠ 0)] at hC
    exact hC rfl
  apply isUnit_iff_ne_zero.mpr
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hC0) (pow_ne_zero _ ht))
    (pow_ne_zero _ hW)

/-- At each actual simple branch the denominator in the Čech residue
is the nonzero derivative of this very sextic. -/
theorem branch_derivative_nonzero (s t x : K)
    (hi : OriginalUniformSparseIgusa318.i10 s t ≠ 0) (hx : eqVal s t x = 0) :
    derVal s t x ≠ 0 := by
  intro hh
  have h := bezout s t x
  rw [hx,hh,mul_zero,mul_zero,zero_add] at h
  exact (isUnit_iff_ne_zero.mp (unit_of_igusa s t hi)) h.symm

theorem coprime_of_igusa (s t : K) (hi : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    IsCoprime (equation s t) ((equation s t).derivative) :=
  relative_coprime s t (unit_of_igusa s t hi)
end Ordinary

end OriginalUniformSparseSmoothChart318

#print axioms OriginalUniformSparseSmoothChart318.branch_derivative_nonzero
#print axioms OriginalUniformSparseSmoothChart318.relative_coprime
#print axioms OriginalUniformSparseSmoothChart318.coprime_of_igusa
