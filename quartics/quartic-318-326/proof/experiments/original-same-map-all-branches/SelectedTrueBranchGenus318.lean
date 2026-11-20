module
public import SelectedTrueBranchDivisor318
public import SelectedSameMapDegreeFinite318
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public section
noncomputable section

open scoped MatrixGroups BigOperators

namespace SelectedTrueBranchGenus318

open SelectedTrueBranchDivisor318 SelectedThreeBranchSignedDegree318

variable {P K : Type*} [Field K] [Algebra ℂ K]
variable (J : K) [finiteCover : FiniteDimensional (IntermediateField.adjoin ℂ ({J} : Set K)) K]
local notation "d" => Module.finrank (IntermediateField.adjoin ℂ ({J} : Set K)) K

include finiteCover in
/-- Canonical divisor degree in the actual branch partition. All
ordinary coefficients are independently zero by all_coefficients.
The supplied fiber-degree rows are sums of true ramification indices
over the three genuine fibers (the complex point weights are one).
The degree field is literally ℂ(J) of the same global function. -/
theorem genus_of_same_map (N : ℕ) [NeZero N] (hN : 4 < N) {g c0 c1728 cinf : ℕ}
    (b : P → Branch) (ord : P → ℤ)
    (coeff : ∀ p, ord p = differentialOrder N (b p))
    (Z : Fin c0 ↪ P) (E : Fin c1728 ↪ P) (C : Fin cinf ↪ P)
    (lift : Fin cinf → SL(2, ℤ))
    (atZero : ∀ i, b (Z i) = .zero)
    (atElliptic : ∀ i, b (E i) = .elliptic)
    (atCusp : ∀ i, b (C i) = .cusp (lift i))
    (fiberZero : (∑ i, ramification N (b (Z i))) = d)
    (fiberElliptic : (∑ i, ramification N (b (E i))) = d)
    (fiberCusp : (∑ i, ramification N (b (C i))) = d)
    (nonemptyCusp : 0 < cinf)
    (canonical : 2*(g:ℤ)-2 = (∑ i, ord (Z i))+(∑ i, ord (E i))+(∑ i, ord (C i)))
    (rank : V N ↪ ℕ) (actualDegree : d = (representatives (primitive N) rank).card) :
    2*d ≤ N^2 ∧ 12*g+6*cinf=d+12 ∧ 2*g-2<d ∧
      (g:ℝ) ≤ (N:ℝ)^2/24+1/2 := by
  have hZeroD : 3*c0=d := by
    simpa [atZero, ramification, nsmul_eq_mul, Nat.mul_comm] using fiberZero
  have hEllipticD : 2*c1728=d := by
    simpa [atElliptic, ramification, nsmul_eq_mul, Nat.mul_comm] using fiberElliptic
  have hCuspD : (∑ i, (ramification N (.cusp (lift i)):ℤ)) = (d:ℤ) := by
    have hD : (∑ i, ramification N (.cusp (lift i))) = d := by
      simpa only [atCusp] using fiberCusp
    exact_mod_cast hD
  have hZ (i : Fin c0) : ord (Z i)=2 := by rw [coeff, atZero, differentialOrder]
  have hE (i : Fin c1728) : ord (E i)=1 := by rw [coeff, atElliptic, differentialOrder]
  have hC (i : Fin cinf) : ord (C i)=-(ramification N (.cusp (lift i)):ℤ)-1 := by
    rw [coeff, atCusp, differentialOrder]
  have sumZ : (∑ i, ord (Z i))=2*(c0:ℤ) := by
    simp [hZ,nsmul_eq_mul,mul_comm]
  have sumE : (∑ i, ord (E i))=(c1728:ℤ) := by
    simp [hE,nsmul_eq_mul]
  have sumC : (∑ i, ord (C i))=-(d:ℤ)-cinf := by
    simp only [hC]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hCuspD] <;> simp [nsmul_eq_mul]
  have hCanonical : 2*(g:ℤ)-2=2*(c0:ℤ)+c1728-d-cinf := by
    rw [sumZ,sumE,sumC] at canonical
    omega
  exact SelectedSameMapDegreeFinite318.degree_genus_cap
    (K := IntermediateField.adjoin ℂ ({J} : Set K)) (F := K) N
    (by omega) rank actualDegree hZeroD hEllipticD nonemptyCusp hCanonical

end SelectedTrueBranchGenus318

#print axioms SelectedTrueBranchGenus318.genus_of_same_map
