module
public import PELOriginalOrderHermitianAdjoint318
public import PELOriginalWholeSectionSpanning318
public section
noncomputable section
namespace PELOriginalFiniteIntegralProductSections318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELPeriodRiemannForm318
open PELOriginalComplementaryHermitian318 PELOriginalComplementaryAutomorphy318
open PELOriginalHermitianForm318 PELOriginalPolarizationAutomorphy318
open PELOriginalPolarizationSemicharacter318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionDescent318 PELOriginalWholeSectionSpanning318
variable (τ : ℂ) (hτ : 0 < τ.im) {ι : Type} [Fintype ι]
variable (u : ι → order) (b : ι → ComplexVectors) (m : ℕ)
variable (hform : ∀ z l,∑ i,form τ hτ (linear (u i) z+b i) (linear (u i) l)=
  (m:ℂ)*form τ hτ z l)
variable (hdiag : ∀ l,∑ i,form τ hτ (linear (u i) l) (linear (u i) l)=
  (m:ℂ)*form τ hτ l l)
variable (hphase : ∀ l : L τ hτ,∃ k : ℤ,
  (∑ i,quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (u i) l)))-
    (m:ℤ)*quadratic ((latticeEquiv τ hτ).symm l)=2*k)
include hform hdiag hphase in
lemma factor_product (l : L τ hτ) (z : ComplexVectors) :
    ∏ i,factor τ hτ (latticeAction τ hτ (u i) l) (linear (u i) z+b i)=
      factor τ hτ l z^m := by
  have h₁ := hform z l.val
  have h₂ := hdiag l.val
  obtain ⟨k,hk⟩ := hphase l
  have hQ := congrArg (fun t : ℤ => (t:ℂ)) hk
  push_cast at hQ
  simp only [factor,←Complex.exp_nat_mul,←Complex.exp_sum]
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨k,?_⟩
  simp only [exponent,latticeAction]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  linear_combination (Real.pi:ℂ)*h₁+(Real.pi:ℂ)/2*h₂+(Real.pi:ℂ)*Complex.I*hQ
variable (N : ℕ) [NeZero N]
@[expose] def value (i : ι → Label N) (z : ComplexVectors) : ℂ :=
  ∏ k,PELOriginalLevelPowerSections318.value τ hτ N (i k) (linear (u k) z+b k)
lemma entire (i : ι → Label N) : Differentiable ℂ (value τ hτ u b N i) := by
  classical
  have he (s : Finset ι) : Differentiable ℂ (fun z =>
      ∏ k∈s,PELOriginalLevelPowerSections318.value τ hτ N (i k) (linear (u k) z+b k)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiable_const (c := (1:ℂ)))
    | @insert k s hk ih =>
      simp only [Finset.prod_insert hk]
      exact ((((holomorphic τ hτ N (i k)).comp
        ((linear (u k)).toContinuousLinearMap.differentiable.add_const (b k)))).mul ih)
  exact he Finset.univ
include hform hdiag hphase in
lemma automorphy (i : ι → Label N) (l : L τ hτ) (z : ComplexVectors) :
    value τ hτ u b N i (z+l.val)=factor τ hτ l z^(N*m)*value τ hτ u b N i z := by
  have he (k : ι) : linear (u k) (z+l.val)+b k=
      (linear (u k) z+b k)+(latticeAction τ hτ (u k) l).val := by
    simp only [map_add,latticeAction]
    abel
  simp only [value,he,original_automorphy,Finset.prod_mul_distrib]
  rw [←Finset.prod_pow,factor_product τ hτ u b m hform hdiag hphase,←pow_mul,Nat.mul_comm m N]
@[expose] def automorphic (i : ι → Label N) : OriginalAutomorphic τ hτ (N*m) where
  value := value τ hτ u b N i
  entire := entire τ hτ u b N i
  lattice_rule := automorphy τ hτ u b m hform hdiag hphase N i
include hform hdiag hphase in
lemma span [NeZero (N*m)] (i : ι → Label N) :
    ∃ c : Label (N*m) → ℂ,∀ z,value τ hτ u b N i z=
      ∑ k,c k*PELOriginalLevelPowerSections318.value τ hτ (N*m) k z := by
  let f := automorphic τ hτ u b m hform hdiag hphase N i
  refine ⟨coordinates τ hτ _ (descend τ hτ _ f),?_⟩
  intro z
  have he := original_lift_expansion τ hτ _ (descend τ hτ _ f) z
  rw [lift_descend] at he
  exact he
end PELOriginalFiniteIntegralProductSections318
