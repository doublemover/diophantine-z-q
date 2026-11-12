module
public import LiteralBasisContent318
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Coprime.Basic
public section
noncomputable section
namespace LiteralSievePolynomial318
open MvPolynomial
set_option maxHeartbeats 2000000
abbrev Poly := MvPolynomial (Fin 3) ℚ

@[expose] def firstP (κ t : ℚ) : Poly := C κ*X 2^2+C (2*t)
@[expose] def productD (t : ℚ) : Poly := (C (t^2)+X 0^2)*(C (t^2)+X 1^2)
@[expose] def secondP (κ t : ℚ) : Poly := C (κ*(t+2))*X 2^2-C 2*X 0*X 1
@[expose] def normK (κ t : ℚ) : Poly :=
  (C κ*X 2^2-X 0*X 1+C (t^2+2*t))^2+C (t^2)*(X 0+X 1)^2

/-- The actual rational polynomials evaluate to the preceding literal
integer-form expressions, not merely to associates with untracked scales. -/
theorem firstP_eval (κ t : ℚ) (v : Fin 3 → ℚ) :
    eval v (firstP κ t)=LiteralAdjacentNormSlice318.P κ t (v 0,v 1,v 2) := by
  simp [firstP,LiteralAdjacentNormSlice318.P]
theorem productD_eval (t : ℚ) (v : Fin 3 → ℚ) :
    eval v (productD t)=LiteralAdjacentNormSlice318.D t (v 0,v 1,v 2) := by
  simp [productD,LiteralAdjacentNormSlice318.D]
theorem secondP_eval (κ t : ℚ) (v : Fin 3 → ℚ) :
    eval v (secondP κ t)=LiteralAdjacentNormSlice318.P' κ t (v 0,v 1,v 2) := by
  simp [secondP,LiteralAdjacentNormSlice318.P']
theorem normK_eval (κ t : ℚ) (v : Fin 3 → ℚ) :
    eval v (normK κ t)=LiteralAdjacentNormSlice318.K κ t (v 0,v 1,v 2) := by
  simp [normK,LiteralAdjacentNormSlice318.K] <;> ring

/-- A divisor cannot acquire a variable absent from a nonzero product.
This uses the actual degree-additivity theorem over the domain. -/
lemma divisor_vars_subset (p q : Poly) (hq : q≠0) (hd : p∣q) : p.vars⊆q.vars := by
  obtain ⟨r,rfl⟩ := hd
  have hp : p≠0 := by intro hh; exact hq (by rw [hh,zero_mul])
  have hr : r≠0 := by intro hh; exact hq (by rw [hh,mul_zero])
  intro i hi
  rw [mem_vars_iff_degreeOf_ne_zero] at hi ⊢
  rw [degreeOf_mul_eq hp hr]
  omega

/-- Disjoint actual variable supports force every common divisor to be a
constant; over Q a nonzero constant is a unit. No Bezout identity is assumed. -/
theorem disjoint_vars_relPrime (p q : Poly) (hp : p≠0) (hq : q≠0)
    (hv : Disjoint p.vars q.vars) : IsRelPrime p q := by
  intro d hdp hdq
  have hd : d≠0 := by
    intro hh
    obtain ⟨r,hr⟩ := hdp
    exact hp (by simpa only [hh,zero_mul] using hr)
  have hvars : d.vars=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact Finset.disjoint_left.mp hv
      (divisor_vars_subset d p hp hdp hi) (divisor_vars_subset d q hq hdq hi)
  have he := vars_eq_empty_iff_eq_C.mp hvars
  have hc : d.coeff 0≠0 := by
    intro hh
    exact hd (by simpa only [hh,map_zero] using he)
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

lemma scaled_power_vars (c : ℚ) (i : Fin 3) (n : ℕ) :
    (C c*X i^n:Poly).vars⊆{i} := by
  intro j hj
  have hm := vars_mul (C c:Poly) (X i^n) hj
  simp only [vars_C,Finset.empty_union] at hm
  exact (show (X i:Poly).vars⊆{i} by simp) (vars_pow (X i:Poly) n hm)

lemma shifted_power_vars (c : ℚ) (i : Fin 3) :
    (C c+X i^2:Poly).vars⊆{i} := by
  intro j hj
  have hm := vars_add_subset (C c:Poly) (X i^2) hj
  simp only [vars_C,Finset.empty_union] at hm
  exact (show (X i:Poly).vars⊆{i} by simp) (vars_pow (X i:Poly) 2 hm)

lemma firstP_vars (κ t : ℚ) : (firstP κ t).vars⊆{2} := by
  intro i hi
  have hm := vars_add_subset (C κ*X 2^2:Poly) (C (2*t)) hi
  simp only [vars_C,Finset.union_empty] at hm
  exact scaled_power_vars κ 2 2 hm
lemma productD_vars (t : ℚ) : (productD t).vars⊆{0,1} := by
  intro i hi
  have hm := vars_mul (C (t^2)+X 0^2:Poly) (C (t^2)+X 1^2) hi
  rcases Finset.mem_union.mp hm with hh|hh
  · have hh' := shifted_power_vars (t^2) 0 hh
    have he : i=0 := by simpa using hh'
    simp [he]
  · have hh' := shifted_power_vars (t^2) 1 hh
    have he : i=1 := by simpa using hh'
    simp [he]

/-- Genuine rational coprimality of the first literal slice's sieve pair.
It is not a conclusion inferred from finite-field point counts. -/
theorem first_pair_relPrime (κ t : ℚ) (ht : t≠0) :
    IsRelPrime (firstP κ t) (productD t) := by
  have hp : firstP κ t≠0 := by
    intro he
    have hh := congrArg (eval (fun _ : Fin 3 => (0:ℚ))) he
    have hz : 2*t=0 := by simpa [firstP] using hh
    exact (mul_ne_zero (by norm_num) ht) hz
  have hq : productD t≠0 := by
    intro he
    have hh := congrArg (eval (fun _ : Fin 3 => (0:ℚ))) he
    have hz : t^2*t^2=0 := by simpa [productD] using hh
    exact (mul_ne_zero (pow_ne_zero 2 ht) (pow_ne_zero 2 ht)) hz
  apply disjoint_vars_relPrime _ _ hp hq
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := firstP_vars κ t hi
  have hj' := productD_vars t hj
  have he : i=2 := by simpa using hi'
  simpa [he] using hj'

end LiteralSievePolynomial318
