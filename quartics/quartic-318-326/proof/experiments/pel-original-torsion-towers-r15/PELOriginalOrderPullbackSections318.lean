module
public import PELOriginalComplementaryAutomorphy318
public import PELOriginalWholePowerRegularization318
public section
noncomputable section
namespace PELOriginalOrderPullbackSections318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalComplementaryAutomorphy318 PELOriginalPolarizationAutomorphy318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPowerSectionDescent318 PELOriginalWholeHZeroDimension318
open PELOriginalSectionMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Columns := Label 3 × Label 3 × Label 3

/-- Genuine fourfold theta pullback along the ORIGINAL order action and
its produced complementary action. The first index will recover the
original target cubic projective point by a rank-one construction. -/
@[expose] def entireValue (a : order) (i : Label 3) (c : Columns)
    (z : ComplexVectors) : ℂ :=
  value τ hτ 3 i (linear a z)*value τ hτ 3 c.1 (linear a z)*
    value τ hτ 3 c.2.1 (linear (complement a) z)*
    value τ hτ 3 c.2.2 (linear (complement a) z)

theorem entire (a : order) (i : Label 3) (c : Columns) :
    Differentiable ℂ (entireValue τ hτ a i c) :=
  ((((holomorphic τ hτ 3 i).comp (linear a).toContinuousLinearMap.differentiable).mul
    ((holomorphic τ hτ 3 c.1).comp (linear a).toContinuousLinearMap.differentiable)).mul
    ((holomorphic τ hτ 3 c.2.1).comp (linear (complement a)).toContinuousLinearMap.differentiable)).mul
    ((holomorphic τ hτ 3 c.2.2).comp (linear (complement a)).toContinuousLinearMap.differentiable)

theorem automorphy (a : order) (i : Label 3) (c : Columns)
    (l : L τ hτ) (z : ComplexVectors) :
    entireValue τ hτ a i c (z+l.val)=
      factor τ hτ l z^(3*(2*degree a))*entireValue τ hτ a i c z := by
  have ha : linear a (z+l.val)=linear a z+(latticeAction τ hτ a l).val := map_add _ _ _
  have hb : linear (complement a) (z+l.val)=linear (complement a) z+
      (latticeAction τ hτ (complement a) l).val := map_add _ _ _
  simp only [entireValue,ha,hb,original_automorphy]
  calc
    _ = (factor τ hτ (latticeAction τ hτ a l) (linear a z)^2 *
        factor τ hτ (latticeAction τ hτ (complement a) l) (linear (complement a) z)^2)^3 *
        (value τ hτ 3 i (linear a z)*value τ hτ 3 c.1 (linear a z)*
          value τ hτ 3 c.2.1 (linear (complement a) z)*value τ hτ 3 c.2.2 (linear (complement a) z)) := by ring
    _ = _ := by
      rw [even_multiplier,←pow_mul]
      rw [Nat.mul_comm (2*degree a) 3]

@[expose] def automorphic (a : order) (i : Label 3) (c : Columns) :
    OriginalAutomorphic τ hτ (3*(2*degree a)) where
  value := entireValue τ hτ a i c
  entire := entire τ hτ a i c
  lattice_rule := automorphy τ hτ a i c

/-- Actual full original H0 section, including a=0 and degree zero.
No theta spanning or projective normal-generation premise is used. -/
@[expose] def pullbackSection (a : order) (i : Label 3) (c : Columns) :
    homogeneous τ hτ (3*(2*degree a)) :=
  ⟨(descend τ hτ (3*(2*degree a)) (automorphic τ hτ a i c)).value,
    (descend τ hτ (3*(2*degree a)) (automorphic τ hτ a i c)).holomorphic⟩

@[expose] def regular (a : order) (j i : Label 3) (c : Columns) :=
  PELOriginalWholePowerRegularization318.linear τ hτ (2*degree a) j (pullbackSection τ hτ a i c)

theorem regular_cover (a : order) (j i : Label 3) (c : Columns)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z j hz (regular τ hτ a j i c)=
      entireValue τ hτ a i c z/(value τ hτ 3 j z)^(2*degree a) := by
  rw [regular,PELOriginalWholePowerRegularization318.cover_evaluation]
  change PELOriginalPowerSectionLift318.lift τ hτ (3*(2*degree a))
    (asSection τ hτ _ (pullbackSection τ hτ a i c)) z / _ = _
  rw [pullbackSection,lift_descend]
  rfl
end PELOriginalOrderPullbackSections318
