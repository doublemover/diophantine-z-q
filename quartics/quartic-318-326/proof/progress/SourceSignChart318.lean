module
public import SourceSignFieldComparison318
public import ContactOverlapMaps318
public import ContactKummerOpenDomain318
public import SchematicEqualityExtension318
public section
noncomputable section
namespace SourceSignChart318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
@[expose] def map (b:Fin 4→Bool):Spec (CommRingCat.of (SourceOrder c))⟶Spec (CommRingCat.of (SourceOrder c)):=
  Spec.map (CommRingCat.ofHom (SourceSignFieldComparison318.sourceEquiv c b).toRingHom)
lemma over_polynomial (b:Fin 4→Bool):map c b≫
    Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder c)))=
      Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder c))):=by
  unfold map
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact (SourceSignFieldComparison318.sourceEquiv c b).commutes p
lemma open_square (b:Fin 4→Bool):
    ContactOverlapMaps318.sourceInclusion c≫map c b=
      ContactGlobalSigns318.openMap c b≫ContactOverlapMaps318.sourceInclusion c:=by
  unfold ContactOverlapMaps318.sourceInclusion map ContactGlobalSigns318.openMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact SourceSignFieldComparison318.order_to_open c b x
local instance sourceDomain:IsDomain (SourceOrder c):=source_domain c
local instance openDomain:IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance sourceIntegral:IsIntegral (Spec (CommRingCat.of (SourceOrder c))):=inferInstance
local instance openNonempty:Nonempty (ContactKummerCover318.cover c):=by
  change Nonempty (Spec (CommRingCat.of (OpenOrder c)))
  infer_instance
local instance inclusionDominant:IsDominant (ContactOverlapMaps318.sourceInclusion c):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (ContactOverlapMaps318.sourceInclusion c).isOpenEmbedding.isOpenMap⟩
local instance inclusionSchematic:IsSchemeTheoreticallyDominant (ContactOverlapMaps318.sourceInclusion c):=
  IsSchemeTheoreticallyDominant.of_isDominant (ContactOverlapMaps318.sourceInclusion c)
local instance modelIntegral:IsIntegralHom (ContactProjectiveModel318.modelMap c):=
  ContactProjectiveModel318.modelMap_integral c
/-- The literal sign on the entire finite source order, including its
ramification fibers, is the restriction of the original whole-source sign. -/
@[reassoc] theorem actual_square (b:Fin 4→Bool):
    map c b≫SourceGlobalAffine318.chartEmbedding c=
      SourceGlobalAffine318.chartEmbedding c≫ContactGlobalSigns318.map c b:=by
  apply SchematicEqualityExtension318.ext (ContactProjectiveModel318.modelMap c)
    (i:=ContactOverlapMaps318.sourceInclusion c)
  · have hc:SourceGlobalAffine318.chartEmbedding c≫ContactProjectiveModel318.modelMap c=
        Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder c)))≫JLineAtlas318.chart ℚ 1:=
      SourceGlobalAffine318.chartEmbedding_over_contact_line c
    rw [Category.assoc,hc,←Category.assoc,over_polynomial,Category.assoc,
      ContactGlobalSigns318.over_line]
    exact hc.symm
  · rw [←Category.assoc,open_square,Category.assoc,ContactOverlapMaps318.source_square,
      ←Category.assoc,ContactOverlapMaps318.source_square,ContactGlobalSigns318.on_open]
end SourceSignChart318
