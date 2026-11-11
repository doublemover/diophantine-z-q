module
public import CubicBoxMonomials318
public section
noncomputable section
namespace HomogeneousRatioBox318
open scoped BigOperators
open CubicBoxMonomials318
variable {ι:Type*}(B:MvPolynomial ι ℂ)(A:Fin 3→MvPolynomial ι ℂ)(m:ℕ)
/-- Every box monomial is cleared to ONE common homogeneous degree.
The leftover denominator power is retained even when some exponents vanish. -/
@[expose] def numerator(a:Box m):MvPolynomial ι ℂ:=
  B^(3*m-total a)*∏i:Fin 3,(A i)^(a i).val
lemma numerator_homogeneous {d:ℕ}(hB:B.IsHomogeneous d)
    (hA:∀i,(A i).IsHomogeneous d)(a:Box m):
    (numerator B A m a).IsHomogeneous (d*(3*m)):=by
  have hp:(∏i:Fin 3,(A i)^(a i).val).IsHomogeneous (∑i:Fin 3,d*(a i).val):=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i hi=>(hA i).pow _)
  have h:=(hB.pow (3*m-total a)).mul hp
  rw [←Finset.mul_sum] at h
  have he:d*(3*m-total a)+d*total a=d*(3*m):=by
    rw [←Nat.mul_add,Nat.sub_add_cancel (total_le a)]
  change (numerator B A m a).IsHomogeneous (d*(3*m-total a)+d*total a) at h
  rwa [he] at h
@[expose] def cleared:(Box m→ℂ)→ₗ[ℂ]MvPolynomial ι ℂ where
  toFun c:=∑a:Box m,c a • numerator B A m a
  map_add' c e:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c e:=by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply]
lemma cleared_homogeneous {d:ℕ}(hB:B.IsHomogeneous d)
    (hA:∀i,(A i).IsHomogeneous d)(c:Box m→ℂ):
    (cleared B A m c).IsHomogeneous (d*(3*m)):=by
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  exact (MvPolynomial.homogeneousSubmodule ι ℂ (d*(3*m))).smul_mem _
    (numerator_homogeneous B A m hB hA a)
/-- Literal field identity before any independence or dimension argument.
Only the ACTUAL common denominator is canceled. -/
lemma numerator_evaluation {K:Type*}[Field K][Algebra ℂ K]
    (F:MvPolynomial ι ℂ→ₐ[ℂ]K)(hB:F B≠0)(a:Box m):
    F (numerator B A m a)=(F B)^(3*m)*∏i:Fin 3,(F (A i)/F B)^(a i).val:=by
  simp only [numerator,map_mul,map_pow,map_prod,div_pow,Finset.prod_div_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  change (F B)^(3*m-total a)*(∏i:Fin 3,F (A i)^(a i).val)=
    (F B)^(3*m)*((∏i:Fin 3,F (A i)^(a i).val)/(F B)^total a)
  have hp:(F B)^(3*m-total a)*(F B)^total a=(F B)^(3*m):=by
    rw [←pow_add,Nat.sub_add_cancel (total_le a)]
  rw [←hp]
  field_simp [hB] <;> ring
/-- The entire finite box combination maps to the genuine polynomial in
the three ratios times a single nonzero denominator power. -/
theorem cleared_evaluation {K:Type*}[Field K][Algebra ℂ K]
    (F:MvPolynomial ι ℂ→ₐ[ℂ]K)(hB:F B≠0)(c:Box m→ℂ):
    F (cleared B A m c)=(F B)^(3*m)*
      MvPolynomial.aeval (fun i=>F (A i)/F B) (polynomial m c):=by
  simp only [cleared,map_sum,map_smul,Algebra.smul_def]
  rw [evaluation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [numerator_evaluation B A m F hB a]
  ring
end HomogeneousRatioBox318
