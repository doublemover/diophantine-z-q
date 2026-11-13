module
public import IntegralOriginalGluingCompatibility318
public import IntegralOriginalChartsProperCover318
public section
noncomputable section
namespace IntegralOriginalModelMorphism318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

/-- The actual morphism from the original integral pushout, obtained using
its original overlap, into the whole-order proper model. -/
@[expose] def map : IntegralGluedModel318.scheme R c ⟶
    IntegralWholeReciprocalGluing318.scheme R c :=
  pushout.desc (IntegralWholeReciprocalGluing318.originalSourceChart R c)
    (IntegralOriginalInfinityEmbedding318.chart R c)
    (IntegralOriginalGluingCompatibility318.chart_agreement R c)
@[simp] theorem finiteChart_map : IntegralGluedModel318.finiteChart R c ≫ map R c =
    IntegralWholeReciprocalGluing318.originalSourceChart R c := pushout.inl_desc ..
@[simp] theorem infinityChart_map : IntegralGluedModel318.infinityChart R c ≫ map R c =
    IntegralOriginalInfinityEmbedding318.chart R c := pushout.inr_desc ..

/-- Surjectivity uses the proved all-prime coverage by the exact original
charts. It is not being used alone as a criterion for scheme isomorphism. -/
theorem surjective : Function.Surjective (map R c) := by
  intro x
  obtain ⟨a,ha⟩ | ⟨b,hb⟩ := IntegralOriginalChartsProperCover318.cover R c x
  · refine ⟨IntegralGluedModel318.finiteChart R c a,?_⟩
    change (IntegralGluedModel318.finiteChart R c ≫ map R c) a=x
    rw [finiteChart_map]
    exact ha
  · refine ⟨IntegralGluedModel318.infinityChart R c b,?_⟩
    change (IntegralGluedModel318.infinityChart R c ≫ map R c) b=x
    rw [infinityChart_map]
    exact hb

/-- The map respects the literal original base structure maps. -/
theorem over_base : map R c ≫ IntegralWholeProjectiveProjection318.structureMap R c =
    IntegralGluedModel318.structureMap R c := by
  apply pushout.hom_ext
  · rw [←Category.assoc,finiteChart_map,IntegralGluedModel318.finiteChart_structure]
    unfold IntegralWholeReciprocalGluing318.originalSourceChart
    rw [Category.assoc,IntegralWholeProjectiveProjection318.finite_structure]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (IntegralWholeFiniteComparison318.comparison R c).symm.commutes r
  · rw [←Category.assoc,infinityChart_map,IntegralGluedModel318.infinityChart_structure]
    unfold IntegralOriginalInfinityEmbedding318.chart
    rw [Category.assoc,IntegralWholeProjectiveProjection318.reciprocal_structure]
    unfold IntegralOriginalInfinityEmbedding318.inclusion
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact IntegralOriginalInfinityEmbedding318.polynomial R c (Polynomial.C r)
end IntegralOriginalModelMorphism318
