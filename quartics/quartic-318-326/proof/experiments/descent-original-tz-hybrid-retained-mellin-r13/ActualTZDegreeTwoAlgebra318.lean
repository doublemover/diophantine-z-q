module
public import Mathlib
public section
noncomputable section
namespace ActualTZDegreeTwoAlgebra318
open MvPolynomial
open scoped BigOperators
variable {σ : Type*}

theorem sumD {J : Type*} (S : Finset J) (f : J→MvPolynomial σ ℤ) (D : ℕ)
    (h : ∀ j∈S,(f j).totalDegree≤D) : (∑ j∈S,f j).totalDegree≤D :=
  totalDegree_finsetSum_le h

theorem addD (P Q : MvPolynomial σ ℤ) (D : ℕ)
    (hP : P.totalDegree≤D) (hQ : Q.totalDegree≤D) : (P+Q).totalDegree≤D :=
  (totalDegree_add P Q).trans (max_le hP hQ)

theorem subD (P Q : MvPolynomial σ ℤ) (D : ℕ)
    (hP : P.totalDegree≤D) (hQ : Q.totalDegree≤D) : (P-Q).totalDegree≤D :=
  (totalDegree_sub P Q).trans (max_le hP hQ)

theorem mulD (P Q : MvPolynomial σ ℤ) (d e : ℕ)
    (hP : P.totalDegree≤d) (hQ : Q.totalDegree≤e) :
    (P*Q).totalDegree≤d+e :=
  (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ)

theorem negD (P : MvPolynomial σ ℤ) (D : ℕ) (hP : P.totalDegree≤D) :
    (-P).totalDegree≤D := by rw [totalDegree_neg]; exact hP

theorem constD (c : ℤ) (D : ℕ) : (C c : MvPolynomial σ ℤ).totalDegree≤D := by
  simp only [totalDegree_C,Nat.zero_le]

theorem varD (i : σ) : (X i : MvPolynomial σ ℤ).totalDegree≤1 := by simp

theorem scaleD (c : ℤ) (P : MvPolynomial σ ℤ) (D : ℕ) (hP : P.totalDegree≤D) :
    (C c*P).totalDegree≤D := by simpa only [Nat.zero_add] using mulD (C c) P 0 D (constD c 0) hP

theorem sqD (P : MvPolynomial σ ℤ) (hP : P.totalDegree≤1) : (P^2).totalDegree≤2 :=
  (totalDegree_pow P 2).trans (Nat.mul_le_mul_left 2 hP)

end ActualTZDegreeTwoAlgebra318
