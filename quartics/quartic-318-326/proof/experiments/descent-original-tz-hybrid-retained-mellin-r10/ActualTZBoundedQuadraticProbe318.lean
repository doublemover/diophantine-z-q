module
public import Mathlib
public section
noncomputable section
namespace ActualTZBoundedQuadraticProbe318
open scoped BigOperators

variable {n : ℕ}

/-- A nonconstant integer polynomial of degree ≤2 differs from
its zero value on the {-1,0,1} box. Uniform finite cardinal, via
pinned total-degree Schwartz–Zippel. -/
theorem bounded_probe (P : MvPolynomial (Fin n) ℤ) (hd : P.totalDegree≤2)
    (hP : ∃ x y : Fin n→ℤ,MvPolynomial.eval x P≠MvPolynomial.eval y P) :
    ∃ x : Fin n→ℤ,(∀ i,|x i|≤1) ∧ MvPolynomial.eval x P≠MvPolynomial.eval 0 P := by
  classical
  let S : Finset ℤ := {-1,0,1}
  let Q := P-MvPolynomial.C (MvPolynomial.eval 0 P)
  have hS : S.card=3 := by decide
  have hQ : Q≠0 := by
    intro h
    have hI : P=MvPolynomial.C (MvPolynomial.eval 0 P) := sub_eq_zero.mp h
    obtain ⟨x,y,hxy⟩ := hP
    apply hxy
    have hx := congrArg (fun R=>MvPolynomial.eval x R) hI
    have hy := congrArg (fun R=>MvPolynomial.eval y R) hI
    simp only [MvPolynomial.eval_C] at hx hy
    exact hx.trans hy.symm
  have hQD : Q.totalDegree≤2 := (MvPolynomial.totalDegree_sub_C_le _ _).trans hd
  by_contra hn
  have hAll (x : Fin n→ℤ) (hx : x∈Fintype.piFinset (fun _ : Fin n=>S)) :
      MvPolynomial.eval x Q=0 := by
    have hBounds (i : Fin n) : |x i|≤1 := by
      have Hz := Fintype.mem_piFinset.mp hx i
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at Hz
      rcases Hz with H|H|H <;> rw [H] <;> norm_num
    have H : MvPolynomial.eval x P=MvPolynomial.eval 0 P := by
      by_contra he
      exact hn ⟨x,hBounds,he⟩
    simp only [Q,map_sub,MvPolynomial.eval_C,H,sub_self]
  have hFilter : (Fintype.piFinset (fun _ : Fin n=>S)).filter (fun x=>MvPolynomial.eval x Q=0)
      =Fintype.piFinset (fun _ : Fin n=>S) := Finset.filter_eq_self.mpr hAll
  have h := MvPolynomial.schwartz_zippel_totalDegree hQ S
  rw [hFilter,Fintype.card_piFinset_const,hS,Nat.cast_pow,div_self (by positivity)] at h
  have hDc : (Q.totalDegree:ℚ≥0)≤2 := by exact_mod_cast hQD
  have H := h.trans (div_le_div_of_nonneg_right hDc (by norm_num : (0:ℚ≥0)≤3))
  norm_num at H

end ActualTZBoundedQuadraticProbe318
