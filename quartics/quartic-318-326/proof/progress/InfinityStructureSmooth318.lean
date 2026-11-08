module
public import InfinityStructureMap318
public section
noncomputable section
namespace InfinityStructureSmooth318
open CategoryTheory AlgebraicGeometry
open InfinityGlobalBase318 InfinityGlobalScheme318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)

theorem baseOpen_over_Q : baseOpen c≫ProjectiveJLine318.structureMap ℚ=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (A c))) := by
  rw [baseOpen,Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1

theorem chartEmbedding_over_Q :
    chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization≫
      ProjectiveJLine318.structureMap ℚ=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (InfinityGlobalChart318.InfinityOrder c))) := by
  rw [←Category.assoc,InfinityStructureMap318.chartEmbedding_over_contact_line,
    Category.assoc,baseOpen_over_Q]
  unfold ReciprocalInfinityNormalization318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (ReciprocalInfinityBase318.chartMap c).map_rat_algebraMap q

/-- The global model's actual structural morphism is smooth on the actual
attached infinity neighborhood. This is a relative-Q statement, not only
an abstract smoothness property of an isomorphic ring. -/
theorem actual_infinity_smooth : Smooth
    (chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization≫
      ProjectiveJLine318.structureMap ℚ) := by
  rw [chartEmbedding_over_Q]
  exact ReciprocalInfinityNormalization318.neighborhood_smooth c
end InfinityStructureSmooth318
