module
public import MixedAdditionGluing318
public section
noncomputable section
namespace SymmetricMixedAddition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def productScheme (A B:R) : Scheme :=
  pullback (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B)
/-- The symmetric mixed-input law is transported through the actual fiber-product symmetry. -/
@[expose] def addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    productScheme A B ⟶ WeierstrassGluing318.scheme A B :=
  (pullbackSymmetry (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B)).hom ≫
    MixedAdditionGluing318.addition A B hD

theorem addition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    addition A B hD ≫ WeierstrassGluing318.structureMap A B=
      pullback.fst (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        ShortAffineScheme318.structureMap A B := by
  rw [addition,Category.assoc,MixedAdditionGluing318.addition_over_base,←Category.assoc,
    pullbackSymmetry_hom_comp_fst]
  exact pullback.condition.symm

@[expose] def rightInfinity (A B:R) : ShortAffineScheme318.scheme A B ⟶ productScheme A B :=
  InfinityInputScheme318.infinityInput A B ≫ InfinityInputScheme318.intoProduct A B ≫
    (pullbackSymmetry (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B)).inv

theorem rightInfinity_fst (A B:R) : rightInfinity A B ≫ pullback.fst _ _=𝟙 _ := by
  rw [rightInfinity,Category.assoc,Category.assoc,pullbackSymmetry_inv_comp_fst]
  exact InfinityInputScheme318.infinityInput_snd A B

theorem rightInfinity_snd (A B:R) : rightInfinity A B ≫ pullback.snd _ _=
    ShortAffineScheme318.structureMap A B ≫ InfinitySmooth318.infinity A B := by
  rw [rightInfinity,Category.assoc,Category.assoc,pullbackSymmetry_inv_comp_snd]
  exact InfinityInputScheme318.infinityInput_fst A B

/-- Actual right identity on the entire finite chart, as a relative Scheme-morphism equation. -/
theorem rightInfinity_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    rightInfinity A B ≫ addition A B hD=WeierstrassGluing318.finiteChart A B := by
  rw [rightInfinity,addition,Category.assoc,Category.assoc,Iso.inv_hom_id_assoc]
  exact MixedAdditionGluing318.infinityInput_addition A B hD
end SymmetricMixedAddition318
