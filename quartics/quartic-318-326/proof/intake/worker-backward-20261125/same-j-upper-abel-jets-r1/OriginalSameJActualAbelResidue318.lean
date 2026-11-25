module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section
noncomputable section

open Polynomial
open scoped LaurentPolynomial BigOperators

namespace OriginalSameJActualAbelResidue318

variable {k : Type*} [Field k] [CharZero k]

def residue (f : k[T;T⁻¹]) : k := f.coeff (-1)

/-- The actual positive Laurent principal part coefficient of t^(j+1)
in log(u/(u-t)), using the Leibniz variable u of the retained chart. -/
def logPart (j : ℕ) : k[T;T⁻¹] :=
  LaurentPolynomial.C (((j+1:ℕ):k)⁻¹) *
    LaurentPolynomial.T (-((j+1:ℕ):ℤ))

omit [CharZero k] in
theorem residue_logPart (f : k[X]) (j : ℕ) :
    residue (f.toLaurent * logPart j) = f.coeff j / ((j+1:ℕ):k) := by
  unfold residue logPart
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_mul_single_apply]
  have hi : (-1:ℤ) + -(-((j+1:ℕ):ℤ)) = (j:ℤ) := by omega
  have hi' : (-1:ℤ) - (-((j+1:ℕ):ℤ)) = (j:ℤ) := by omega
  first | rw [hi] | rw [hi']
  rw [LaurentPolynomial.coeff_toLaurent]
  change (f.toFinsupp.coeff.mapDomain Nat.castEmbedding) (Nat.castEmbedding j) *
    (((j+1:ℕ):k)⁻¹) = _
  rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective,
    Polynomial.toFinsupp_apply, ←div_eq_mul_inv]

def formalAbel (f : k[X]) (m : ℕ) : k[X] :=
  ∑ j ∈ Finset.range m,
    monomial (j+1) (residue (f.toLaurent * logPart j))

omit [CharZero k] in
theorem formalAbel_coeff (f : k[X]) {m j : ℕ} (hj : j<m) :
    (formalAbel f m).coeff (j+1) = f.coeff j / ((j+1:ℕ):k) := by
  rw [formalAbel,Polynomial.finsetSum_coeff,Finset.sum_eq_single j]
  · rw [Polynomial.coeff_monomial_same,residue_logPart]
  · intro i _ hi
    exact Polynomial.coeff_monomial_of_ne _ (fun h => hi (Nat.add_right_cancel h).symm)
  · intro h
    exact (h (Finset.mem_range.mpr hj)).elim

/-- Differentiation of the actual residue coordinates has exactly the
original truncated coefficient of the regular form. No factorial or
unmarked scalar occurs here. -/
theorem actual_abel_derivative (f : k[X]) {m j : ℕ} (hj : j<m) :
    (formalAbel f m).derivative.coeff j = f.coeff j := by
  rw [Polynomial.coeff_derivative,formalAbel_coeff f hj]
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))

theorem invariant_mod_order (f g : k[X]) {m : ℕ}
    (same : (X:k[X])^m ∣ f-g) :
    ∀ j<m, (formalAbel f m).derivative.coeff j =
      (formalAbel g m).derivative.coeff j := by
  intro j hj
  rw [actual_abel_derivative _ hj,actual_abel_derivative _ hj]
  have h := Polynomial.X_pow_dvd_iff.mp same j hj
  rw [Polynomial.coeff_sub] at h
  exact sub_eq_zero.mp h

end OriginalSameJActualAbelResidue318

#print axioms OriginalSameJActualAbelResidue318.residue_logPart
#print axioms OriginalSameJActualAbelResidue318.formalAbel_coeff
#print axioms OriginalSameJActualAbelResidue318.actual_abel_derivative
#print axioms OriginalSameJActualAbelResidue318.invariant_mod_order
