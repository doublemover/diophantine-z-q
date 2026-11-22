module
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Ring.Parity
public section
noncomputable section

namespace ActualGaussianWeberRelativeFrobFactor318

open Polynomial

section PolynomialQuotient

variable {K F : Type*} [Field K] [Field F]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- No degree bound: zero derivative over perfect coefficients makes
the actual polynomial a p-th power, not merely a function on F_p. -/
theorem polynomial_pth_root (A : K[X]) (hA : A.derivative = 0) :
    ∃ A₀ : K[X], A₀ ^ p = A := by
  refine ⟨(A.contract p).map (frobeniusEquiv K p).symm, ?_⟩
  calc
    _ = expand K p (A.contract p) := (polynomial_expand_eq K p (A.contract p)).symm
    _ = A := expand_contract p hA (Fact.out : p.Prime).ne_zero

/-- Both roots are obtained in precisely the same polynomial ring.
Their evaluations have the stated quotient even over a nonperfect
ambient field, in particular the original function field. -/
theorem quotient_pth_root (f : K[X] →+* F) {A B : K[X]}
    (hA : A.derivative = 0) (hB : B.derivative = 0) (hDen : f B ≠ 0) :
    ∃ A₀ B₀ : K[X], f B₀ ≠ 0 ∧ (f A₀ / f B₀) ^ p = f A / f B := by
  obtain ⟨A₀, hA₀⟩ := polynomial_pth_root A hA
  obtain ⟨B₀, hB₀⟩ := polynomial_pth_root B hB
  have h₀ : f B₀ ≠ 0 := by
    intro hz
    apply hDen
    rw [← hB₀, map_pow, hz, zero_pow (Fact.out : p.Prime).ne_zero]
  refine ⟨A₀, B₀, h₀, ?_⟩
  calc
    _ = f (A₀^p) / f (B₀^p) := by simp only [div_pow, map_pow]
    _ = _ := by rw [hA₀,hB₀]

end PolynomialQuotient

section LiteralCubic

variable {F : Type*} [Field F]
variable {p : ℕ} [Fact p.Prime]

private theorem pth_root_from_square (hodd : Odd p) {v c : F}
    (h : v^2 = c^p) : ∃ z : F, z^p = v := by
  have hp₀ : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  by_cases hc : c = 0
  · have hv : v = 0 := by
      by_contra hn
      apply pow_ne_zero 2 hn
      simpa only [hc,zero_pow hp₀] using h
    exact ⟨0, by rw [zero_pow hp₀,hv]⟩
  · obtain ⟨m,hm⟩ := hodd
    have hp : p = 1+2*m := hm.trans (Nat.add_comm _ _)
    have e : v^p = v*(c^m)^p := by
      calc
        _ = v^(1+2*m) := congrArg (fun n : ℕ => v^n) hp
        _ = v*(v^2)^m := by rw [pow_add,pow_one,pow_mul]
        _ = _ := by rw [h,← pow_mul,Nat.mul_comm p m,pow_mul]
    refine ⟨v/c^m, ?_⟩
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero p (pow_ne_zero m hc))).2 e

variable [CharP F p]

/-- The other ordinate does not need its own derivative identity.
The square relation and odd p force its p-th root in the same field.
The unique roots satisfy the original literal cubic. -/
theorem cubic_coordinates_pth_roots (hodd : Odd p) {u v U : F}
    (hU : U^p = u) (hE : v^2 = u^3-u) :
    ∃ V : F, V^p = v ∧ V^2 = U^3-U := by
  have hU' : frobenius F p U = u := hU
  have hW : frobenius F p (U^3-U) = u^3-u := by rw [map_sub,map_pow,hU']
  obtain ⟨V,hV⟩ := pth_root_from_square hodd (hE.trans hW.symm)
  have hV' : frobenius F p V = v := hV
  refine ⟨V,hV,?_⟩
  apply (frobenius F p).injective
  rw [map_pow,hV',hW,hE]

end LiteralCubic

/-- This is the exact coordinate bridge used on the literal generic
Weber cubic after the coprime cross-derivative argument. There is
no degree cap, morphology or finite-field point-agreement premise. -/
theorem cubic_point_factors {K F : Type*} [Field K] [Field F]
    {p : ℕ} [Fact p.Prime] [CharP K p] [PerfectRing K p] [CharP F p]
    (hodd : Odd p) (f : K[X] →+* F) {A B : K[X]} (v : F)
    (hA : A.derivative = 0) (hB : B.derivative = 0) (hDen : f B ≠ 0)
    (hE : v^2 = (f A / f B)^3 - (f A / f B)) :
    ∃ U V : F, U^p = f A/f B ∧ V^p = v ∧ V^2 = U^3-U := by
  obtain ⟨A₀,B₀,_,hU⟩ := quotient_pth_root f hA hB hDen
  obtain ⟨V,hV,hcurve⟩ := cubic_coordinates_pth_roots hodd hU hE
  exact ⟨f A₀/f B₀,V,hU,hV,hcurve⟩

end ActualGaussianWeberRelativeFrobFactor318
