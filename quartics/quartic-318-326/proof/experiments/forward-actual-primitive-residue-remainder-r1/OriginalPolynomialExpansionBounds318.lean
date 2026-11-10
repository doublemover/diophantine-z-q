module
public import OriginalReducedPolynomialProducer318
public section
noncomputable section
namespace OriginalPolynomialExpansionBounds318
open scoped BigOperators
open MvPolynomial LiteralSievePolynomial318 TernaryQuadraticLineCover318
set_option maxHeartbeats 4000000

/-- A concrete finite monomial expansion, retaining multiplicities until
coefficients are collected. This lets triangle inequalities prove genuine
coefficient heights without assuming a bound on polynomial support. -/
structure Expansion where
  Index : Type
  finite : Fintype Index
  exponent : Index → (Fin 3 →₀ ℕ)
  coefficient : Index → ℚ
attribute [instance] Expansion.finite

@[expose] def polynomial (e : Expansion) : Poly := ∑ i, monomial (e.exponent i) (e.coefficient i)
@[expose] def weight (e : Expansion) : ℝ := ∑ i, |(e.coefficient i:ℝ)|

lemma weight_nonneg (e : Expansion) : 0≤weight e := Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- Every actual collected coefficient is bounded by the expansion's
explicit total absolute coefficient weight, even when monomials repeat. -/
theorem coefficient_le_weight (e : Expansion) (d : Fin 3 →₀ ℕ) :
    |((polynomial e).coeff d:ℝ)|≤weight e := by
  classical
  rw [polynomial,MvPolynomial.coeff_sum]
  push_cast
  calc
    |∑ i, ((monomial (e.exponent i) (e.coefficient i):Poly).coeff d:ℝ)|≤
        ∑ i, |((monomial (e.exponent i) (e.coefficient i):Poly).coeff d:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ weight e := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [MvPolynomial.coeff_monomial]
      split_ifs <;> simp

@[expose] def constExpansion (a : ℚ) : Expansion where
  Index := Unit
  finite := inferInstance
  exponent := fun _ => 0
  coefficient := fun _ => a

@[expose] def addExpansion (e f : Expansion) : Expansion where
  Index := e.Index ⊕ f.Index
  finite := inferInstance
  exponent := Sum.elim e.exponent f.exponent
  coefficient := Sum.elim e.coefficient f.coefficient

@[expose] def mulExpansion (e f : Expansion) : Expansion where
  Index := e.Index × f.Index
  finite := inferInstance
  exponent := fun i => e.exponent i.1+f.exponent i.2
  coefficient := fun i => e.coefficient i.1*f.coefficient i.2

lemma polynomial_const (a : ℚ) : polynomial (constExpansion a)=C a := by
  simp [polynomial,constExpansion,C_apply]
lemma weight_const (a : ℚ) : weight (constExpansion a)=|(a:ℝ)| := by simp [weight,constExpansion]
lemma polynomial_add (e f : Expansion) : polynomial (addExpansion e f)=polynomial e+polynomial f := by
  simp [polynomial,addExpansion,Fintype.sum_sum_type]
lemma weight_add (e f : Expansion) : weight (addExpansion e f)=weight e+weight f := by
  simp [weight,addExpansion,Fintype.sum_sum_type]
lemma polynomial_mul (e f : Expansion) : polynomial (mulExpansion e f)=polynomial e*polynomial f := by
  simp [polynomial,mulExpansion,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum,monomial_mul_monomial]
lemma weight_mul (e f : Expansion) : weight (mulExpansion e f)=weight e*weight f := by
  simp [weight,mulExpansion,Fintype.sum_prod_type,Rat.cast_mul,abs_mul,Finset.sum_mul,Finset.mul_sum]

@[expose] def linearExpansion (a : Vector ℚ) : Expansion where
  Index := Fin 3
  finite := inferInstance
  exponent := fun i => Finsupp.single i 1
  coefficient := ![a.1,a.2.1,a.2.2]

lemma polynomial_linear (a : Vector ℚ) :
    polynomial (linearExpansion a)=OriginalReducedPolynomialEquiv318.linear a := by
  simp [polynomial,linearExpansion,Fin.sum_univ_succ,←C_mul_X_eq_monomial,
    OriginalReducedPolynomialEquiv318.linear,add_assoc]
lemma weight_linear (a : Vector ℚ) : weight (linearExpansion a)=
    |(a.1:ℝ)|+|(a.2.1:ℝ)|+|(a.2.2:ℝ)| := by
  simp [weight,linearExpansion,Fin.sum_univ_succ,add_assoc]

end OriginalPolynomialExpansionBounds318
