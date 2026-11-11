module
public import PELOriginalLevelPowerSections318
public import PELOriginalPowerSectionDescent318
public import PELOriginalSectionMultiplication318
public section
noncomputable section
namespace PELOriginalBalancedPowerSections318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318
open PELOriginalPolarizationAutomorphy318 PELOriginalPowerSectionDescent318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The two translated ORIGINAL factors balance exactly, including the
semicharacter and the quadratic correction. No flat factor is dropped. -/
lemma balanced_factor (l : L τ hτ) (z a : ComplexVectors) :
    factor τ hτ l (z+a)*factor τ hτ l (z-a)=factor τ hτ l z^2 := by
  simp only [factor,pow_two,←Complex.exp_add]
  congr 1
  have hn : form τ hτ (-a) l.val= -form τ hτ a l.val :=
    (PELOriginalHermitianForm318.linear τ hτ l.val).map_neg a
  simp only [exponent,sub_eq_add_neg,form_add_left,hn]
  ring

/-- Arbitrary genuine original degree-N sections, translated in opposite
directions, produce a genuine section of degree 2N. -/
@[expose] def balanced (N : ℕ) (a : ComplexVectors)
    (f g : OriginalAutomorphic τ hτ N) : OriginalAutomorphic τ hτ (2*N) where
  value z := f.value (z+a)*g.value (z-a)
  entire := (f.entire.comp (differentiable_id.add_const a)).mul
    (g.entire.comp (differentiable_id.sub_const a))
  lattice_rule l z := by
    have hp : z+l.val+a=(z+a)+l.val := by abel
    have hm : z+l.val-a=(z-a)+l.val := by abel
    rw [hp,hm,f.lattice_rule,g.lattice_rule]
    calc
      _ = (factor τ hτ l (z+a)*factor τ hτ l (z-a))^N *
          (f.value (z+a)*g.value (z-a)) := by rw [mul_pow]; ring
      _ = _ := by rw [balanced_factor,←pow_mul]

variable (N : ℕ) [NeZero N]
@[expose] def thetaAutomorphic (i : Label N) : OriginalAutomorphic τ hτ N where
  value := PELOriginalLevelPowerSections318.value τ hτ N i
  entire := holomorphic τ hτ N i
  lattice_rule := original_automorphy τ hτ N i

@[expose] def balancedTheta (a : ComplexVectors) (i j : Label N) :
    OriginalAutomorphic τ hτ (2*N) :=
  balanced τ hτ N a (thetaAutomorphic τ hτ N i) (thetaAutomorphic τ hτ N j)

@[expose] def section (a : ComplexVectors) (i j : Label N) : homogeneous τ hτ (2*N) :=
  ⟨(descend τ hτ (2*N) (balancedTheta τ hτ N a i j)).value,
    (descend τ hτ (2*N) (balancedTheta τ hτ N a i j)).holomorphic⟩

lemma lift_section (a : ComplexVectors) (i j : Label N) (z : ComplexVectors) :
    PELOriginalPowerSectionLift318.lift τ hτ (2*N)
      (asSection τ hτ (2*N) (section τ hτ N a i j)) z=
    PELOriginalLevelPowerSections318.value τ hτ N i (z+a)*
      PELOriginalLevelPowerSections318.value τ hτ N j (z-a) := by
  exact lift_descend τ hτ (2*N) (balancedTheta τ hτ N a i j) z

lemma swap (a z : ComplexVectors) (i j : Label N) :
    (balancedTheta τ hτ N (-a) j i).value z=(balancedTheta τ hτ N a i j).value z := by
  change PELOriginalLevelPowerSections318.value τ hτ N j (z+-a)*
    PELOriginalLevelPowerSections318.value τ hτ N i (z- -a)=_
  simp only [sub_neg_eq_add,←sub_eq_add_neg]
  exact mul_comm _ _
end PELOriginalBalancedPowerSections318
