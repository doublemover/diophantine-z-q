module
public import CompletedUnitMaps318
public import FiniteChartSchematicDensity318
public section
noncomputable section
namespace CompletedAdditionUnits318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 CompletedAdditionRestrictions318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
theorem rightUnit_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    rightUnit A B ≫ CompletedAddition318.addition A B hD=𝟙 (scheme A B) := by
  apply FiniteChartSchematicDensity318.hom_ext_to_completed A B A B
  · simp only [Category.assoc,CompletedAddition318.addition_over_base,rightUnit_fst_assoc,Category.id_comp]
  · rw [←Category.assoc,finite_rightUnit,Category.assoc,inputChart_addition,Category.comp_id]
    exact SymmetricMixedAddition318.rightInfinity_addition A B hD

theorem leftUnit_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    leftUnit A B ≫ CompletedAddition318.addition A B hD=𝟙 (scheme A B) := by
  apply FiniteChartSchematicDensity318.hom_ext_to_completed A B A B
  · simp only [Category.assoc,CompletedAddition318.addition_over_base,leftUnit_fst_assoc,
      infinity_section,Category.comp_id,Category.id_comp]
  · rw [←Category.assoc,finite_leftUnit,Category.assoc,inputChart_addition,Category.comp_id]
    exact MixedAdditionGluing318.infinityInput_addition A B hD
end CompletedAdditionUnits318
