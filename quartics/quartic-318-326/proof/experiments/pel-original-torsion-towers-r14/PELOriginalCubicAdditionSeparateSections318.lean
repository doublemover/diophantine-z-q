module
public import PELOriginalLevelThetaNegation318
public import PELOriginalWholeSectionSpanning318
public import PELOriginalBalancedThetaProducts318
public section
noncomputable section
namespace PELOriginalCubicAdditionSeparateSections318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationAutomorphy318 PELOriginalPowerSectionDescent318
open PELOriginalWholeSectionSpanning318 PELOriginalHermitianForm318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual characteristic-wise addition/difference product in the
original cubic polarization gauge. -/
@[expose] def paired (r s : Label 3) (z a : ComplexVectors) : ℂ :=
  value τ hτ 3 r (z+a) * value τ hτ 3 s (z-a)

lemma balanced_factors (l : L τ hτ) (z a : ComplexVectors) :
    factor τ hτ l (z+a) * factor τ hτ l (z-a) = factor τ hτ l z ^ 2 := by
  have h := PELOriginalBalancedThetaProducts318.product_factors τ hτ Finset.univ
    (PELOriginalBalancedThetaProducts318.pair a) l z
  simpa [PELOriginalBalancedThetaProducts318.pair,Fin.prod_univ_two,Fin.sum_univ_two,
    sub_eq_add_neg,form,zero_left] using h

lemma paired_holomorphic (r s : Label 3) (a : ComplexVectors) :
    Differentiable ℂ (fun z => paired τ hτ r s z a) :=
  ((PELOriginalLevelPowerSections318.holomorphic τ hτ 3 r).comp
    (differentiable_id.add_const a)).mul
      ((PELOriginalLevelPowerSections318.holomorphic τ hτ 3 s).comp
        (differentiable_id.sub_const a))

lemma paired_automorphy (r s : Label 3) (a : ComplexVectors)
    (l : L τ hτ) (z : ComplexVectors) :
    paired τ hτ r s (z+l.val) a = factor τ hτ l z ^ 6 * paired τ hτ r s z a := by
  have ha : z+l.val+a = (z+a)+l.val := by abel
  have hb : z+l.val-a = (z-a)+l.val := by abel
  simp only [paired,ha,hb,PELOriginalLevelPowerSections318.original_automorphy]
  calc
    _ = (factor τ hτ l (z+a)*factor τ hτ l (z-a))^3 *
        (value τ hτ 3 r (z+a)*value τ hτ 3 s (z-a)) := by ring
    _ = _ := by rw [balanced_factors]; ring

/-- Every translated cubic pair is a produced full original degree-six
section. No finite theta-span hypothesis appears in its construction. -/
@[expose] def pairedAutomorphic (r s : Label 3) (a : ComplexVectors) :
    OriginalAutomorphic τ hτ 6 where
  value z := paired τ hτ r s z a
  entire := paired_holomorphic τ hτ r s a
  lattice_rule := paired_automorphy τ hτ r s a

lemma paired_swap (r s : Label 3) (z a : ComplexVectors) :
    paired τ hτ r s z a = paired τ hτ r (-s) a z := by
  have h : z-a = -(a-z) := by abel
  simp only [paired,h,PELOriginalLevelThetaNegation318.value_neg,add_comm]

/-- Actual separate spanning in the first variable follows from full
original H0, not from an assumed addition formula. -/
theorem first_span (r s : Label 3) (a : ComplexVectors) :
    ∃ c : Label 6 → ℂ, ∀ z : ComplexVectors,
      paired τ hτ r s z a = ∑ u : Label 6, c u * value τ hτ 6 u z := by
  let f := pairedAutomorphic τ hτ r s a
  refine ⟨coordinates τ hτ 6 (descend τ hτ 6 f),?_⟩
  intro z
  have h := original_lift_expansion τ hτ 6 (descend τ hτ 6 f) z
  rw [lift_descend] at h
  exact h

/-- The second-variable span retains the negated second characteristic;
individual cubic coordinates are not incorrectly treated as even. -/
theorem second_span (r s : Label 3) (z : ComplexVectors) :
    ∃ c : Label 6 → ℂ, ∀ a : ComplexVectors,
      paired τ hτ r s z a = ∑ v : Label 6, c v * value τ hτ 6 v a := by
  obtain ⟨c,hc⟩ := first_span τ hτ r (-s) z
  exact ⟨c,fun a => (paired_swap τ hτ r s z a).trans (hc a)⟩
end PELOriginalCubicAdditionSeparateSections318
