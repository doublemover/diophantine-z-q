module
public import PELOriginalOrderPullbackSections318
public import PELOriginalCubeBasisCoefficients318
public section
noncomputable section
namespace PELOriginalOrderEvenThetaSections318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalComplementaryAutomorphy318 PELOriginalPolarizationAutomorphy318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionDescent318 PELOriginalWholeHZeroDimension318 PELOriginalSectionMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N]
@[expose] def entireValue (a : order) (i j : Label N) (z : ComplexVectors) : ℂ :=
  value τ hτ N i (linear a z)^2*value τ hτ N j (linear (complement a) z)^2
lemma entire (a : order) (i j : Label N) : Differentiable ℂ (entireValue τ hτ N a i j) :=
  (((holomorphic τ hτ N i).comp (linear a).toContinuousLinearMap.differentiable).pow 2).mul
    (((holomorphic τ hτ N j).comp (linear (complement a)).toContinuousLinearMap.differentiable).pow 2)
lemma automorphy (a : order) (i j : Label N) (l : L τ hτ) (z : ComplexVectors) :
    entireValue τ hτ N a i j (z+l.val)=
      factor τ hτ l z^(N*(2*degree a))*entireValue τ hτ N a i j z := by
  have ha : linear a (z+l.val)=linear a z+(latticeAction τ hτ a l).val := map_add _ _ _
  have hb : linear (complement a) (z+l.val)=linear (complement a) z+
      (latticeAction τ hτ (complement a) l).val := map_add _ _ _
  simp only [entireValue,ha,hb,original_automorphy,mul_pow]
  calc
    _ = (factor τ hτ (latticeAction τ hτ a l) (linear a z)^2*
        factor τ hτ (latticeAction τ hτ (complement a) l) (linear (complement a) z)^2)^N*
        (value τ hτ N i (linear a z)^2*value τ hτ N j (linear (complement a) z)^2) := by
      rw [mul_pow,←pow_mul,←pow_mul]
      rw [Nat.mul_comm 2 N]
      ring
    _ = _ := by rw [even_multiplier,←pow_mul,Nat.mul_comm (2*degree a) N]
@[expose] def automorphic (a : order) (i j : Label N) : OriginalAutomorphic τ hτ (N*(2*degree a)) where
  value := entireValue τ hτ N a i j
  entire := entire τ hτ N a i j
  lattice_rule := automorphy τ hτ N a i j
@[expose] def section (a : order) (i j : Label N) : homogeneous τ hτ (N*(2*degree a)) :=
  ⟨(descend τ hτ _ (automorphic τ hτ N a i j)).value,
    (descend τ hτ _ (automorphic τ hτ N a i j)).holomorphic⟩
lemma lift_section (a : order) (i j : Label N) (z : ComplexVectors) :
    PELOriginalPowerSectionLift318.lift τ hτ _ (asSection τ hτ _ (section τ hτ N a i j)) z=
      entireValue τ hτ N a i j z := lift_descend τ hτ _ (automorphic τ hτ N a i j) z
end PELOriginalOrderEvenThetaSections318
