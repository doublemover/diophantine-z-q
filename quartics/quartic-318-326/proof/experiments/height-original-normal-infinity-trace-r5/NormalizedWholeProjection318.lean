module
public import NormalizedWholeScalarMaps318
public section
noncomputable section
namespace NormalizedWholeProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizedWholeOverlap318 NormalizedWholeScalarMaps318
open NormalizedWholeGluing318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)
@[expose] def finiteProjection : finiteScheme R d a ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (FiniteOrder R d a))) ≫
    JLineAtlas318.chart R 1
@[expose] def reciprocalProjection : infinityScheme R d a ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (InfinityOrder R d a))) ≫ JLineAtlas318.chart R 0

theorem overlap_agreement : intoFinite R d a ≫ finiteProjection R d a=
    intoInfinity R d a ≫ reciprocalProjection R d a := by
  unfold intoFinite intoInfinity finiteProjection reciprocalProjection
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  have hf := finite_evaluation R d a
  have hi := infinity_evaluation R d a
  change Spec.map (CommRingCat.ofHom
      ((NormalizedWholeOpenMaps318.finiteMap R d a).comp
        (algebraMap (Polynomial R) (FiniteOrder R d a)))) ≫ _ =
    Spec.map (CommRingCat.ofHom
      ((NormalizedWholeOpenMaps318.infinityMap R d a).comp
        (algebraMap (Polynomial R) (InfinityOrder R d a)))) ≫ _
  rw [hf,hi]
  exact JLineOverlap318.unit_chart_overlap (R:=R) (commonT R d a)

/-- A morphism of the actual whole-order pushout to the actual proper
projective line, with original t and reciprocal w=1/t coordinates on its two charts. -/
@[expose] def projection : scheme R d a ⟶ ProjectiveJLine318.scheme R :=
  pushout.desc (finiteProjection R d a) (reciprocalProjection R d a) (overlap_agreement R d a)

@[simp] theorem finite_restriction : finiteChart R d a ≫ projection R d a=finiteProjection R d a :=
  pushout.inl_desc ..
@[simp] theorem reciprocal_restriction : infinityChart R d a ≫ projection R d a=reciprocalProjection R d a :=
  pushout.inr_desc ..

/-- The structure morphism is the composite with the original projective
line's structure map. Properness of this composite is not presumed. -/
@[expose] def structureMap : scheme R d a ⟶ Spec (CommRingCat.of R) :=
  projection R d a ≫ ProjectiveJLine318.structureMap R

theorem finite_structure : finiteChart R d a ≫ structureMap R d a=
    Spec.map (CommRingCat.ofHom (algebraMap R (FiniteOrder R d a))) := by
  rw [structureMap,←Category.assoc,finite_restriction,finiteProjection,Category.assoc,
    JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1

theorem reciprocal_structure : infinityChart R d a ≫ structureMap R d a=
    Spec.map (CommRingCat.ofHom (algebraMap R (InfinityOrder R d a))) := by
  rw [structureMap,←Category.assoc,reciprocal_restriction,reciprocalProjection,Category.assoc,
    JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
end NormalizedWholeProjection318
