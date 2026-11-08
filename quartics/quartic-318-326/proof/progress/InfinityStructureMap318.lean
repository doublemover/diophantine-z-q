module
public import NormalizationBaseCompatibility318
public section
noncomputable section
namespace InfinityStructureMap318
open CategoryTheory AlgebraicGeometry
open InfinityGlobalBase318 InfinityGlobalChart318 InfinityGlobalScheme318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance sourceAlgebra : Algebra (A c) (Source c):=(sourceHom c).toAlgebra
local instance infinityAlgebra : Algebra (A c) (InfinityOrder c):=
  (ReciprocalInfinityBase318.chartMap c).toAlgebra

theorem baseSections_square :
    (ContactProjectiveModel318.coverMap c).fromNormalization.app (baseOpen c ''ᵁ ⊤)≫
      CommRingCat.ofHom (actualChartEquiv c).toRingHom=
    (NormalizationChart318.targetSections (baseOpen c)).hom≫
      CommRingCat.ofHom (ReciprocalInfinityBase318.chartMap c) := by
  exact NormalizationBaseCompatibility318.factored_sections_base_trans
    (C:=CommRingCat.of (InfinityOrder c)) (CommRingCat.ofHom (sourceHom c)) (baseOpen c)
    (ContactProjectiveModel318.coverMap c) (factorization c) (sourceClosureEquiv c)

/-- The actual infinity open immersion commutes with the actual global
normalization morphism to the contact line. -/
theorem chartEmbedding_over_contact_line :
    chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization=
      ReciprocalInfinityNormalization318.structureMap c≫baseOpen c := by
  exact NormalizationBaseCompatibility318.factored_chart_over_base
    (C:=CommRingCat.of (InfinityOrder c)) (CommRingCat.ofHom (sourceHom c)) (baseOpen c)
    (ContactProjectiveModel318.coverMap c) (factorization c) (sourceClosureEquiv c)

end InfinityStructureMap318
