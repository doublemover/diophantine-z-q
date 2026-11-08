module
public import CompletedCoefficientProduct318
public import CompletedIteratedAddition318
public section
noncomputable section
namespace CompletedAdditionCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 WeierstrassCoefficientMap318 CompletedCoefficientProduct318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S

lemma mapped_discriminant (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsUnit (-16*(4*(a A)^3+27*(a B)^2)) := by
  simpa only [map_neg,map_mul,map_add,map_pow,map_ofNat] using hD.map a

/-- The actual completed addition commutes with every coefficient algebra,
including nonreduced bases. Equality extends from the entire finite product
by schematic density, not by evaluation on field points. -/
theorem addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    pair (S:=S) A B ≫ CompletedAddition318.addition A B hD=
      CompletedAddition318.addition (a A) (a B) hS ≫ coefficientMap A B := by
  letI:=FiniteProductSchematicDensity318.pairMap_dense (a A) (a B) hS
  letI:=CubicClosedImmersion318.structure_proper A B
  apply SchematicEqualityExtension318.ext (structureMap A B) ?_ (FiniteProductSchematicDensity318.pairMap (a A) (a B))
  · rw [←Category.assoc,finite_pair,Category.assoc,finite_restriction,
      ←Category.assoc,finite_restriction,finite_addition]
  · simp only [Category.assoc,CompletedAddition318.addition_over_base,pair_fst_assoc,
      coefficientMap_base]
    simp only [←Category.assoc,CompletedAddition318.addition_over_base]

open CompletedIteratedAddition318
lemma diagonal_pair (A B:R) : diagonal (a A) (a B) ≫ pair (S:=S) A B=
    coefficientMap A B ≫ diagonal A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,pair_fst,diagonal_fst,diagonal_fst_assoc,Category.id_comp,Category.comp_id]
  · simp only [Category.assoc,pair_snd,diagonal_snd,diagonal_snd_assoc,Category.id_comp,Category.comp_id]

/-- Equality of the actual doubling composites, with the original
coefficient morphism on both sides. -/
theorem doubling (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    coefficientMap (S:=S) A B ≫ CompletedIteratedAddition318.doubling A B hD=
      CompletedIteratedAddition318.doubling (a A) (a B) hS ≫ coefficientMap A B := by
  rw [CompletedIteratedAddition318.doubling,←Category.assoc,←diagonal_pair,Category.assoc,
    addition A B hD hS,←Category.assoc]
  rfl

lemma tripleInputs_pair (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    tripleInputs (a A) (a B) hS ≫ pair (S:=S) A B=
      coefficientMap A B ≫ tripleInputs A B hD := by
  apply pullback.hom_ext
  · rw [Category.assoc,pair_fst,tripleInputs_fst_assoc,Category.assoc,tripleInputs_fst]
    exact (doubling A B hD hS).symm
  · simp only [Category.assoc,pair_snd,tripleInputs_snd,tripleInputs_snd_assoc,Category.id_comp,Category.comp_id]

/-- The actual tripling morphism commutes with arbitrary coefficient
base change. No group axiom over the changed coefficient ring is assumed. -/
theorem tripling (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    coefficientMap (S:=S) A B ≫ CompletedIteratedAddition318.tripling A B hD=
      CompletedIteratedAddition318.tripling (a A) (a B) hS ≫ coefficientMap A B := by
  rw [CompletedIteratedAddition318.tripling,←Category.assoc,←tripleInputs_pair A B hD hS,
    Category.assoc,addition A B hD hS,←Category.assoc]
  rfl
end CompletedAdditionCoefficient318
