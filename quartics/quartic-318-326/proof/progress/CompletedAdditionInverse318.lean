module
public import CompletedAntiDiagonal318
public import FiniteChartSchematicDensity318
public section
noncomputable section
namespace CompletedAdditionInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 CompletedAdditionRestrictions318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
/-- Actual global right-inverse identity, obtained from the checked finite
identity by schematic density, without discarding nilpotent directions. -/
theorem antiDiagonal_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    antiDiagonal A B ≫ CompletedAddition318.addition A B hD=structureMap A B ≫ infinity A B := by
  apply FiniteChartSchematicDensity318.hom_ext_to_completed A B A B
  · simp only [Category.assoc,CompletedAddition318.addition_over_base,antiDiagonal_fst_assoc,
      Category.id_comp,infinity_section,Category.comp_id]
  · rw [←Category.assoc,finite_antiDiagonal,Category.assoc,inputChart_addition]
    change FiniteInverseScheme318.antiDiagonal A B ≫ FiniteAdditionGluing318.addition A B hD=
      finiteChart A B ≫ structureMap A B ≫ infinity A B
    rw [FiniteInverseScheme318.antiDiagonal_addition,←Category.assoc,finiteChart_structure]
end CompletedAdditionInverse318
