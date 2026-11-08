module
public import InfinityPrimeSignInertia318
public import SourceSignChart318
public section
noncomputable section
namespace InfinitySignChart318
open AlgebraicGeometry CategoryTheory
open InfinityReciprocalAction318
set_option maxHeartbeats 550000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance chartAlgebra:Algebra (Base c) (Order c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance chartSMul:SMul (Base c) (Order c):=(chartAlgebra c).toSMul
local instance chartModule:Module (Base c) (Order c):=Algebra.toModule
@[expose] def map (b:Fin 4→Bool):
    ReciprocalInfinityNormalization318.neighborhood c⟶ReciprocalInfinityNormalization318.neighborhood c:=
  Spec.map (CommRingCat.ofHom (InfinitySignCoordinates318.sign c b).toRingHom)
lemma over_reciprocal (b:Fin 4→Bool):
    map c b≫ReciprocalInfinityNormalization318.structureMap c=
      ReciprocalInfinityNormalization318.structureMap c:=by
  unfold map ReciprocalInfinityNormalization318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (InfinitySignCoordinates318.sign c b).commutes x

lemma open_square (b:Fin 4→Bool):
    ContactOverlapMaps318.infinityInclusion c≫map c b=
      ContactGlobalSigns318.openMap c b≫ContactOverlapMaps318.infinityInclusion c:=by
  unfold ContactOverlapMaps318.infinityInclusion map ContactGlobalSigns318.openMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply SourceOpenFractionField318.openEmbedding_injective c
  change SourceOpenFractionField318.openEmbedding c
      (InfinityOverlapLocalization318.toOpen c (InfinitySignCoordinates318.sign c b x))=
    SourceOpenFractionField318.openEmbedding c
      (ContactGlobalSigns318.openEquiv c b (InfinityOverlapLocalization318.toOpen c x))
  rw [InfinityOverlapLocalization318.toOpen_embedding,InfinitySignCoordinates318.original_square,
    SourceSignFieldComparison318.open_embedding,InfinityOverlapLocalization318.toOpen_embedding]

local instance infinityDomain:IsDomain (Order c):=InfinityOpenChart318.openOrder_domain c
local instance infinityIntegral:IsIntegral (ReciprocalInfinityNormalization318.neighborhood c):=by
  change IsIntegral (Spec (CommRingCat.of (Order c)))
  infer_instance
local instance sourceDomain:IsDomain (ContactKummerOrder318.OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance sourceNonempty:Nonempty (ContactKummerCover318.cover c):=by
  change Nonempty (Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)))
  infer_instance
local instance inclusionDominant:IsDominant (ContactOverlapMaps318.infinityInclusion c):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (ContactOverlapMaps318.infinityInclusion c).isOpenEmbedding.isOpenMap⟩
local instance inclusionSchematic:IsSchemeTheoreticallyDominant (ContactOverlapMaps318.infinityInclusion c):=
  IsSchemeTheoreticallyDominant.of_isDominant (ContactOverlapMaps318.infinityInclusion c)
local instance modelIntegral:IsIntegralHom (ContactProjectiveModel318.modelMap c):=
  ContactProjectiveModel318.modelMap_integral c
/-- The constructed whole reciprocal-chart action is the restriction of
the actual original global normalization sign, with the exact chart embedding. -/
@[reassoc] theorem actual_square (b:Fin 4→Bool):
    map c b≫InfinityGlobalScheme318.chartEmbedding c=
      InfinityGlobalScheme318.chartEmbedding c≫ContactGlobalSigns318.map c b:=by
  apply SchematicEqualityExtension318.ext (ContactProjectiveModel318.modelMap c)
    (i:=ContactOverlapMaps318.infinityInclusion c)
  · have hc:InfinityGlobalScheme318.chartEmbedding c≫ContactProjectiveModel318.modelMap c=
        ReciprocalInfinityNormalization318.structureMap c≫InfinityGlobalBase318.baseOpen c:=
      InfinityStructureMap318.chartEmbedding_over_contact_line c
    rw [Category.assoc,hc,←Category.assoc,over_reciprocal,Category.assoc,
      ContactGlobalSigns318.over_line]
    exact hc.symm
  · rw [←Category.assoc,open_square,Category.assoc,ContactOverlapMaps318.infinity_square,
      ←Category.assoc,ContactOverlapMaps318.infinity_square,ContactGlobalSigns318.on_open]
end InfinitySignChart318
