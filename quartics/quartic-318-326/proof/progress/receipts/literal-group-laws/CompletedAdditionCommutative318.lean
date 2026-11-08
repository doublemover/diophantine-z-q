module
public import CompletedAdditionRestrictions318
public import FiniteProductSchematicDensity318
public import FiniteProductSymmetry318
public section
noncomputable section
namespace CompletedAdditionCommutative318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 CompletedAdditionRestrictions318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
theorem inputChart_eq_pairMap (A B:R) : inputChart A B 0 0=FiniteProductSchematicDensity318.pairMap A B := by
  apply pullback.hom_ext
  · rw [inputChart_fst,FiniteProductSchematicDensity318.pairMap_fst]
    rfl
  · rw [inputChart_snd,FiniteProductSchematicDensity318.pairMap_snd]
    rfl
theorem pairMap_symmetry (A B:R) :
    FiniteProductSchematicDensity318.pairMap A B ≫ (pullbackSymmetry (structureMap A B) (structureMap A B)).hom=
      (pullbackSymmetry (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)).hom ≫
        FiniteProductSchematicDensity318.pairMap A B := by
  apply pullback.hom_ext
  · rw [Category.assoc,pullbackSymmetry_hom_comp_fst,
      FiniteProductSchematicDensity318.pairMap_snd,Category.assoc,
      FiniteProductSchematicDensity318.pairMap_fst,←Category.assoc,pullbackSymmetry_hom_comp_fst]
  · rw [Category.assoc,pullbackSymmetry_hom_comp_snd,
      FiniteProductSchematicDensity318.pairMap_fst,Category.assoc,
      FiniteProductSchematicDensity318.pairMap_snd,←Category.assoc,pullbackSymmetry_hom_comp_snd]

/-- Global commutativity of the actual completed-curve addition over any
commutative base with unit discriminant, retaining nilpotent directions. -/
theorem addition_commutative (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    (pullbackSymmetry (structureMap A B) (structureMap A B)).hom ≫ CompletedAddition318.addition A B hD=
      CompletedAddition318.addition A B hD := by
  apply FiniteProductSchematicDensity318.pair_hom_ext_to_completed A B A B hD
  · rw [Category.assoc,CompletedAddition318.addition_over_base,←Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact pullback.condition.symm
  · rw [←Category.assoc,pairMap_symmetry,Category.assoc,←inputChart_eq_pairMap,
      inputChart_addition]
    exact FiniteProductSymmetry318.addition_commutative A B hD
end CompletedAdditionCommutative318
