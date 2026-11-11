module
public import IntegralPencilScalarMaps318
public section
noncomputable section
namespace IntegralWholePencilMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralPencilScalarMaps318
open IntegralWholeReciprocalGluing318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def finiteProjection : finiteScheme R c ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (finiteCoordinate R c).toRingHom) ≫
    JLineAtlas318.chart R 1
@[expose] def reciprocalProjection : infinityScheme R c ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (CommRingCat.ofHom (reciprocalCoordinate R c).toRingHom) ≫ JLineAtlas318.chart R 0

theorem overlap_agreement : intoFinite R c ≫ finiteProjection R c=
    intoInfinity R c ≫ reciprocalProjection R c := by
  unfold intoFinite intoInfinity finiteProjection reciprocalProjection
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  have hf := finite_evaluation R c
  have hi := reciprocal_evaluation R c
  change Spec.map (CommRingCat.ofHom
      ((IntegralWholeOrderOpenMaps318.finiteMap R c).comp
        (finiteCoordinate R c).toRingHom)) ≫ _ =
    Spec.map (CommRingCat.ofHom
      ((IntegralWholeOrderOpenMaps318.infinityMap R c).comp
        (reciprocalCoordinate R c).toRingHom)) ≫ _
  rw [hf,hi]
  exact JLineOverlap318.unit_chart_overlap (R:=R) (originalTUnit R c)

/-- A morphism of the actual whole-order pushout to the actual proper
projective line, with original t=c0^-1*y0² and reciprocal t^-1=c0^-1*u² coordinates.
This is the contact pencil, not the auxiliary y0 projection. -/
@[expose] def projection : scheme R c ⟶ ProjectiveJLine318.scheme R :=
  pushout.desc (finiteProjection R c) (reciprocalProjection R c) (overlap_agreement R c)

@[simp] theorem finite_restriction : finiteChart R c ≫ projection R c=finiteProjection R c :=
  pushout.inl_desc ..
@[simp] theorem reciprocal_restriction : infinityChart R c ≫ projection R c=reciprocalProjection R c :=
  pushout.inr_desc ..

/-- The structure morphism is the composite with the original projective
line's structure map. Properness of this composite is not presumed. -/
@[expose] def structureMap : scheme R c ⟶ Spec (CommRingCat.of R) :=
  projection R c ≫ ProjectiveJLine318.structureMap R

theorem finite_structure : finiteChart R c ≫ structureMap R c=
    Spec.map (CommRingCat.ofHom (algebraMap R (FiniteOrder R c))) := by
  rw [structureMap,←Category.assoc,finite_restriction,finiteProjection,Category.assoc,
    JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (finiteCoordinate R c).commutes

theorem reciprocal_structure : infinityChart R c ≫ structureMap R c=
    Spec.map (CommRingCat.ofHom (algebraMap R (InfinityOrder R c))) := by
  rw [structureMap,←Category.assoc,reciprocal_restriction,reciprocalProjection,Category.assoc,
    JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (reciprocalCoordinate R c).commutes
end IntegralWholePencilMap318
