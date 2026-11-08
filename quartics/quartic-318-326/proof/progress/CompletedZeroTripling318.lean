module
public import CompletedAdditionUnits318
public import CompletedIteratedAddition318
public import WeierstrassBaseChange318
import all WeierstrassGluing318
public section
noncomputable section
namespace CompletedZeroTripling318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma diagonal_origin : WeierstrassGluing318.infinity A B ≫ CompletedIteratedAddition318.diagonal A B=
    WeierstrassGluing318.infinity A B ≫ CompletedAdditionUnits318.rightUnit A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedIteratedAddition318.diagonal_fst,
      CompletedAdditionUnits318.rightUnit_fst,Category.comp_id]
  · simp only [Category.assoc,CompletedIteratedAddition318.diagonal_snd,
      CompletedAdditionUnits318.rightUnit_snd,Category.comp_id]
    rw [←Category.assoc,WeierstrassGluing318.infinity_section,Category.id_comp]
lemma doubling_origin : WeierstrassGluing318.infinity A B ≫ CompletedIteratedAddition318.doubling A B hD=
    WeierstrassGluing318.infinity A B := by
  rw [CompletedIteratedAddition318.doubling,←Category.assoc,diagonal_origin,Category.assoc,
    CompletedAdditionUnits318.rightUnit_addition,Category.comp_id]
lemma tripleInputs_origin : WeierstrassGluing318.infinity A B ≫ CompletedIteratedAddition318.tripleInputs A B hD=
    WeierstrassGluing318.infinity A B ≫ CompletedAdditionUnits318.rightUnit A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedIteratedAddition318.tripleInputs_fst,
      CompletedAdditionUnits318.rightUnit_fst,Category.comp_id,doubling_origin]
  · simp only [Category.assoc,CompletedIteratedAddition318.tripleInputs_snd,
      CompletedAdditionUnits318.rightUnit_snd,Category.comp_id]
    rw [←Category.assoc,WeierstrassGluing318.infinity_section,Category.id_comp]
/-- Actual tripling fixes the actual infinity section over arbitrary bases. -/
theorem tripling_origin : WeierstrassGluing318.infinity A B ≫ CompletedIteratedAddition318.tripling A B hD=
    WeierstrassGluing318.infinity A B := by
  rw [CompletedIteratedAddition318.tripling,←Category.assoc,tripleInputs_origin,Category.assoc,
    CompletedAdditionUnits318.rightUnit_addition,Category.comp_id]

/-- The actual zero section is disjoint from the whole finite chart. -/
theorem origin_preimage_finite : WeierstrassGluing318.infinity A B ⁻¹ᵁ
    (WeierstrassGluing318.finiteChart A B).opensRange=⊥ := by
  rw [WeierstrassGluing318.infinity,Scheme.Hom.comp_preimage,WeierstrassBaseChange318.infinity_preimage_finite]
  unfold InfinitySmooth318.infinity
  rw [SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen ((InfinityChart318.origin A B) (InfinityChart318.z A B))=⊥
  rw [InfinityChart318.origin_z,PrimeSpectrum.basicOpen_zero]
end CompletedZeroTripling318
