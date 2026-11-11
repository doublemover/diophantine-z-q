module
public import PELOriginalAllLevelProjectiveMap318
public import PELOriginalWholeSectionSpanning318
public import EntireBalancedTripleRigidity318
public section
noncomputable section
namespace PELOriginalTripleEvaluation318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationPowerBundle318
open PELOriginalPowerSectionLift318 PELOriginalPowerSectionDescent318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalWholeSectionSpanning318 PELOriginalAllLevelProjectiveMap318
open PELOriginalBalancedThetaProducts318
variable (τ:ℂ)(hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- Equality of the actual level-three projective coordinates forces
ONE common proportionality scalar for evaluation of EVERY genuine
original section. Whole H0 spanning, not only independence, is consumed. -/
theorem all_sections_proportional(x y:ComplexVectors)
    (h:projectiveMap τ hτ 1 (projection (P τ) x)=
      projectiveMap τ hτ 1 (projection (P τ) y)):
    ∃C:ℂ,C≠0∧∀s:HolomorphicSection τ hτ 3,
      lift τ hτ 3 s x=C*lift τ hτ 3 s y:=by
  rw [original_covering_square,original_covering_square] at h
  obtain ⟨C,hC⟩:=(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hc:C≠0:=by
    intro hz
    apply coverVector_nonzero τ hτ 1 x
    rw [←hC,hz,zero_smul]
  refine ⟨C,hc,?_⟩
  intro s
  rw [original_lift_expansion,original_lift_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have he:value τ hτ 3 r x=C*value τ hτ 3 r y:=
    (congrFun hC r).symm
  rw [he]
  ring

@[expose] def shifts(a b:ComplexVectors):Fin 3→ComplexVectors:=![a,b,-a-b]
lemma balanced(a b:ComplexVectors):∑j,shifts a b j=0:=by
  simp only [shifts,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  abel
@[expose] def tripleFunction(a b:ComplexVectors):OriginalAutomorphic τ hτ 3 where
  value:=product τ hτ 3 (shifts a b)
  entire:=product_holomorphic τ hτ 3 (shifts a b)
  lattice_rule:=PELOriginalBalancedThetaProducts318.original_automorphy τ hτ 3
    (shifts a b) (balanced a b)
lemma triple_formula(a b z:ComplexVectors):
    (tripleFunction τ hτ a b).value z=F (z+a)*F (z+b)*F (z+(-a-b)):=by
  simp only [tripleFunction,product,shifts,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  ring

/-- Genuine balanced triple identity on ALL shifts, including points
where theta vanishes. It comes from the actual same-bundle sections and
one projective evaluation scalar, not a quotient defined away from zeros. -/
theorem triple_proportional(x y:ComplexVectors)
    (h:projectiveMap τ hτ 1 (projection (P τ) x)=
      projectiveMap τ hτ 1 (projection (P τ) y)):
    ∃C:ℂ,C≠0∧∀a b:ComplexVectors,
      F (x+a)*F (x+b)*F (x+(-a-b))=C*(F (y+a)*F (y+b)*F (y+(-a-b))):=by
  obtain ⟨C,hC,he⟩:=all_sections_proportional τ hτ x y h
  refine ⟨C,hC,?_⟩
  intro a b
  have hs:=he (descend τ hτ 3 (tripleFunction τ hτ a b))
  rw [lift_descend,lift_descend,triple_formula,triple_formula] at hs
  exact hs
end PELOriginalTripleEvaluation318
