module
public import ActualTwoDescentSimultaneousLocalClasses318
public import Mathlib.NumberTheory.Padics.Hensel
public section
noncomputable section
namespace ActualTwoDescentHenselSquare318
open Polynomial
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- An actual square root in the p-adic integers, obtained from the pinned
Hensel theorem for the literal polynomial X²-A. -/
theorem actual_hensel_square (A z : ℤ_[p])
    (h : ‖z^2-A‖ < ‖2*z‖^2) : ∃ r : ℤ_[p], r^2=A := by
  let F : Polynomial ℤ_[p] := X^2-C A
  have hF (x : ℤ_[p]) : F.aeval x=x^2-A := by simp [F]
  have hd (x : ℤ_[p]) : F.derivative.aeval x=2*x := by
    simp [F,Polynomial.derivative_pow]
  have hh : ‖F.aeval z‖ < ‖F.derivative.aeval z‖^2 := by
    rw [hF,hd]
    exact h
  obtain ⟨r,hr,_,_,_⟩ := hensels_lemma (F:=F) (a:=z) hh
  refine ⟨r,sub_eq_zero.mp ?_⟩
  rwa [hF] at hr

/-- An odd-prime unit root modulo p lifts to a genuine p-adic root.
The explicit divisibility hypothesis is on the integer residual. -/
theorem actual_odd_square_lift (hp2 : p ≠ 2) (A x : ℕ)
    (hx : Nat.Coprime p x) (hdiv : (p : ℤ) ∣ (x : ℤ)^2-A) :
    ∃ r : ℤ_[p], r^2=(A : ℤ_[p]) := by
  have h2 : ‖(2 : ℤ_[p])‖=1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
  have hxn : ‖(x : ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr hx
  have hres : ‖(x : ℤ_[p])^2-A‖ < 1 := by
    have h := (PadicInt.norm_int_lt_one_iff_dvd ((x : ℤ)^2-A)).mpr hdiv
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_natCast] using h
  apply actual_hensel_square (A : ℤ_[p]) (x : ℤ_[p])
  simpa only [norm_mul,h2,hxn,one_mul,one_pow] using hres

end ActualTwoDescentHenselSquare318
