module
public import PELOriginalThetaLineSection318
public section
noncomputable section
namespace PELOriginalBalancedThetaProducts318
open QuaternionicRealPeriod318 PELOriginalPolarizationAutomorphy318
open PELOriginalHermitianForm318
variable (τ:ℂ) (hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

lemma factor_translate (l:L τ hτ) (z a:ComplexVectors):
    factor τ hτ l (z+a)=factor τ hτ l z*
      Complex.exp ((Real.pi:ℂ)*form τ hτ a l.val):=by
  simp only [factor,exponent,form_add_left]
  rw [←Complex.exp_add]
  congr 1
  ring

/-- The extra flat factor of an individual translate is retained. It
cancels only for a genuinely balanced family, not for arbitrary translates. -/
lemma product_factors {ι:Type*} (s:Finset ι) (a:ι→ComplexVectors)
    (l:L τ hτ) (z:ComplexVectors):
    (∏j∈s,factor τ hτ l (z+a j))=
      factor τ hτ l z^s.card*
        Complex.exp ((Real.pi:ℂ)*form τ hτ (∑j∈s,a j) l.val):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form,PELOriginalHermitianForm318.zero_left]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj,Finset.sum_insert hj,Finset.card_insert_of_not_mem hj,
      factor_translate,ih,pow_succ,form_add_left,mul_add,Complex.exp_add]
    ring

@[expose] def product (n:ℕ) (a:Fin n→ComplexVectors) (z:ComplexVectors):ℂ:=
  ∏j,F (z+a j)
lemma product_holomorphic (n:ℕ) (a:Fin n→ComplexVectors):
    Differentiable ℂ (product τ hτ n a):=by
  classical
  have h:∀s:Finset (Fin n),Differentiable ℂ (fun z=>∏j∈s,F (z+a j)):=by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (differentiable_const (1:ℂ))
    | @insert j s hj ih =>
      simpa only [Finset.prod_insert hj] using
        ((PELOriginalGaugedTheta318.holomorphic τ hτ).comp
          (differentiable_id.add_const (a j))).mul ih
  exact h Finset.univ

/-- Entire balanced translated products have EXACTLY the n-th power
of the original Appell-Humbert multiplier on the full original lattice. -/
theorem original_automorphy (n:ℕ) (a:Fin n→ComplexVectors)
    (ha:∑j,a j=0) (l:L τ hτ) (z:ComplexVectors):
    product τ hτ n a (z+l.val)=factor τ hτ l z^n*product τ hτ n a z:=by
  classical
  simp only [product,show ∀j:Fin n,z+l.val+a j=(z+a j)+l.val from fun j=>by abel,
    PELOriginalGaugedTheta318.original_automorphy,Finset.prod_mul_distrib]
  have hp:=product_factors τ hτ Finset.univ a l z
  simp only [Finset.card_univ,Fintype.card_fin,ha,form,
    PELOriginalHermitianForm318.zero_left,Complex.ofReal_zero,mul_zero,sub_zero,
    Complex.exp_zero,mul_one] at hp
  rw [hp]
lemma product_nonzero_iff (n:ℕ) (a:Fin n→ComplexVectors) (z:ComplexVectors):
    product τ hτ n a z≠0↔∀j,F (z+a j)≠0:=by
  classical
  simp [product]

/-- Concrete balanced pairs, suitable for generation of the square of
this SAME original line; no accidental flat twist survives. -/
@[expose] def pair (a:ComplexVectors):Fin 2→ComplexVectors:=![a,-a]
lemma pair_balanced (a:ComplexVectors):∑j,pair a j=0:=by
  simp [pair,Fin.sum_univ_two]
lemma pair_value (a z:ComplexVectors):
    product τ hτ 2 (pair a) z=F (z+a)*F (z-a):=by
  simp [product,pair,Fin.prod_univ_two,sub_eq_add_neg]
end PELOriginalBalancedThetaProducts318
