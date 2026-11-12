module
public import PELOriginalSquareGeneration318
public import Mathlib.Algebra.BigOperators.Fin
public section
noncomputable section
namespace PELOriginalHigherPowerGeneration318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalBalancedThetaProducts318
variable (τ:ℂ) (hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- n+1 equal shifts and one compensating shift; total degree n+2.
The compensating factor is essential to stay on the original line power. -/
@[expose] def shifts (n:ℕ) (a:ComplexVectors):Fin (n+2)→ComplexVectors:=
  Fin.snoc (fun _:Fin (n+1)=>a) (-((n+1:ℕ):ℂ) • a)
lemma balanced (n:ℕ) (a:ComplexVectors):∑j,shifts n a j=0:=by
  simp [shifts,Fin.sum_snoc,Nat.cast_smul_eq_nsmul]
lemma product_formula (n:ℕ) (a z:ComplexVectors):
    product τ hτ (n+2) (shifts n a) z=
      F (z+a)^(n+1)*F (z-((n+1:ℕ):ℂ) • a):=by
  classical
  rw [product,Fin.prod_univ_castSucc]
  simp [shifts,sub_eq_add_neg]

/-- Actual higher-power avoidance reduces to TWO nontrivial entire
functions, irrespective of n; repeated factors retain their multiplicity. -/
theorem exists_translated_nonzero (n:ℕ) (z:ComplexVectors):
    ∃a,product τ hτ (n+2) (shifts n a) z≠0:=by
  obtain ⟨p,hp⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  let c:ℂ:=((n+1:ℕ):ℂ)
  have hc:c≠0:=by exact_mod_cast Nat.succ_ne_zero n
  have hf:Differentiable ℂ (fun a:ComplexVectors=>F (z+a)):=
    (PELOriginalGaugedTheta318.holomorphic τ hτ).comp
      (differentiable_const.add differentiable_id)
  have hg:Differentiable ℂ (fun a:ComplexVectors=>F (z-c • a)):=
    (PELOriginalGaugedTheta318.holomorphic τ hτ).comp
      (differentiable_const.sub (differentiable_id.const_smul c))
  have hfn:∃a,F (z+a)≠0:=by
    refine ⟨p-z,?_⟩
    rw [show z+(p-z)=p by abel]
    exact hp
  have hgn:∃a,F (z-c • a)≠0:=by
    refine ⟨c⁻¹ • (z-p),?_⟩
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul,sub_sub_cancel]
    exact hp
  obtain ⟨a,ha⟩:=EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero
    (fun a=>F (z+a)) (fun a=>F (z-c • a)) hf hg hfn hgn
  have hh: F (z+a)≠0 ∧ F (z-c • a)≠0:=mul_ne_zero_iff.mp ha
  refine ⟨a,?_⟩
  rw [product_formula]
  exact mul_ne_zero (pow_ne_zero _ hh.1) hh.2

@[expose] def higherSection (n:ℕ) (a:ComplexVectors) (q:Base τ):PowerTotal τ hτ (n+2):=
  powerSection τ hτ (n+2) (product τ hτ (n+2) (shifts n a)) q
lemma continuous (n:ℕ) (a:ComplexVectors):Continuous (higherSection τ hτ n a):=
  continuous_section τ hτ (n+2) _ (product_holomorphic τ hτ (n+2) (shifts n a)).continuous
    (original_automorphy τ hτ (n+2) (shifts n a) (balanced n a))
lemma holomorphic_in_original_charts (n:ℕ) (a c:ComplexVectors):
    DifferentiableOn ℂ (fun z:ComplexVectors=>((powerCore τ hτ (n+2)).localTriv c
      (higherSection τ hτ n a (projection (P τ) z))).2) (chart τ hτ c).target:=
  holomorphic_section τ hτ (n+2) _ (product_holomorphic τ hτ (n+2) (shifts n a))
    (original_automorphy τ hτ (n+2) (shifts n a) (balanced n a)) c

/-- Every power of degree at least TWO is basepoint-free on the actual
original compact torus, by explicitly produced balanced theta products.
This does not assert that these maps separate points or tangent vectors. -/
theorem all_powers_basepoint_free (n:ℕ) (q:Base τ):
    ∃a,(higherSection τ hτ n a q).2≠0:=by
  exact exists_translated_nonzero τ hτ n
    (chart τ hτ ((core τ hτ).indexAt q) q)
theorem evaluation_surjective (n:ℕ) (q:Base τ) (v:PowerFiber τ hτ (n+2) q):
    ∃a:ComplexVectors,∃c:ℂ,c*(higherSection τ hτ n a q).2=v:=by
  obtain ⟨a,ha⟩:=all_powers_basepoint_free τ hτ n q
  exact ⟨a,v/(higherSection τ hτ n a q).2,div_mul_cancel₀ v ha⟩
end PELOriginalHigherPowerGeneration318
