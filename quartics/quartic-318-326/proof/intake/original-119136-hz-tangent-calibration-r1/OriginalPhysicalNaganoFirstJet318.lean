module
public import OriginalPhysicalNaganoReadback318
public import Mathlib.Algebra.Polynomial.Derivative
public section
namespace OriginalPhysicalNaganoFirstJet318
open Polynomial OriginalMarkedIntPolynomialCertificate318 OriginalPhysicalNaganoJet318
open OriginalPhysicalNaganoReadback318
@[expose] def mulIdx (n : ℕ) : List ℤ → List ℤ
  | [] => []
  | c::l => (n*c)::mulIdx (n+1) l
@[expose] def dcoeff (l : List ℤ) : List ℤ := mulIdx 1 l.tail

theorem idx_step {R : Type*} [CommRing R] (z : R) (n : ℕ) (l : List ℤ) :
    horner z (mulIdx (n+1) l) = horner z (mulIdx n l) + horner z l := by
  induction l generalizing n with
  | nil => simp [mulIdx,horner]
  | cons c l ih =>
    simp only [mulIdx,horner,Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast,Nat.cast_add,Nat.cast_one]
    rw [ih (n+1)]
    ring

theorem idx_zero {R : Type*} [CommRing R] (z : R) (l : List ℤ) :
    horner z (mulIdx 0 l) = z * horner z (dcoeff l) := by cases l <;> simp [dcoeff,mulIdx,horner]

theorem derivative_literal (l : List ℤ) :
    derivative (horner (X : ℤ[X]) l) = horner X (dcoeff l) := by
  induction l with
  | nil => simp [dcoeff,mulIdx,horner]
  | cons a l ih =>
    change derivative ((a:ℤ[X]) + X*horner X l) = horner X (mulIdx 1 l)
    rw [derivative_add, derivative_intCast, derivative_mul, derivative_X, ih, zero_add,one_mul,
      show horner (X : ℤ[X]) (mulIdx 1 l) = horner X (mulIdx 0 l)+horner X l from idx_step _ 0 l, idx_zero]
    exact add_comm _ _

theorem exact_coeffs : dcoeff aa=ap ∧ dcoeff bb=bp ∧ dcoeff cc=cp ∧ dcoeff nn=np ∧ dcoeff dd=dp := by decide +kernel

variable {K : Type*} [Field K] [CharZero K]
noncomputable def dH (z : K) (l : List ℤ) : K := (derivative (horner (X : ℤ[X]) l)).eval₂ (Int.castRingHom K) z
omit [CharZero K] in
theorem eval_derivative (z : K) (l : List ℤ) : dH z l = h z (dcoeff l) := by
  unfold dH h
  rw [derivative_literal]
  have hom := OriginalPhysicalHZ210Map318.horner_map (eval₂RingHom (Int.castRingHom K) z) (X:ℤ[X]) (dcoeff l)
  rw [← OriginalPhysicalHZ210Identity318.horner_eq, ← OriginalPhysicalHZ210Identity318.horner_eq] at hom
  simpa using hom

omit [CharZero K] in
theorem jac_is_derivative (z : K) :
    W z = dH z nn*h z dd-h z nn*dH z dd := by
  rw [eval_derivative,eval_derivative,exact_coeffs.2.2.2.1,exact_coeffs.2.2.2.2]
  rfl

/-- A first jet of the actual two rational functions, formed **before** specializing
the field point. There is no fictitious nonzero ℚ-derivation of its number field. -/
theorem marked_jet (z : K) (hz : h z qq=0) :
    ((dH z bb*h z aa-3*h z bb*dH z aa)*(h z dd)^2) /
      (108000*(h z aa)^4*(dH z nn*h z dd-h z nn*dH z dd)) = r z rdx rdxD ∧
    ((dH z cc*h z aa-5*h z cc*dH z aa)*(h z dd)^2) /
      (5443200000*(h z aa)^6*(dH z nn*h z dd-h z nn*dH z dd)) = r z rdy rdyD := by
  rw [← jac_is_derivative, eval_derivative,eval_derivative,eval_derivative,exact_coeffs.1,
      exact_coeffs.2.1, exact_coeffs.2.2.1]
  exact ⟨rdx_eq z hz,rdy_eq z hz⟩
end OriginalPhysicalNaganoFirstJet318
#print axioms OriginalPhysicalNaganoFirstJet318.marked_jet
