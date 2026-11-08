module
public import CharacterFifthCommonMultiple318
public import FifthInfinityInvariantRestriction318
public import DifferentialFunctor318
public section
noncomputable section
namespace CharacterInfinityLocalForm318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev I:=InfinityOpenChart318.OpenOrder units
abbrev O:=ContactKummerOrder318.OpenOrder units
abbrev L:=FifthCharacterField318.L
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
abbrev u:I:=InfinityOrderCoordinates318.coordinate units
abbrev lift:I→ₐ[ℚ]O:=ContactOverlapAlgebraMaps318.infinityMap units
@[expose] def rootTimesU (i:Fin 4):I:=
  algebraMap ℚ I (units 0:ℚ)*InfinityCharacterUnits318.indexedRatio units i
lemma rootTimesU_unit (i:Fin 4):IsUnit (rootTimesU i):=
  ((units 0).isUnit.map (algebraMap ℚ I)).mul (InfinityCharacterUnits318.indexedRatio_unit units i)
lemma raw_lift (a:I):SourceOpenFractionField318.openEmbedding units (lift a)=
    InfinityOpenFractionField318.openEmbedding units a:=InfinityOverlapLocalization318.toOpen_embedding units a
/-- The pole of each original root is canceled by the literal ramified u,
with a genuine unit on the entire infinity chart. -/
lemma root_relation (i:Fin 4):lift (rootTimesU i)=lift u*ContactRootReciprocals318.openRoot units i:=by
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [map_mul,raw_lift,raw_lift,ContactRootReciprocals318.open_embedding_root,
    rootTimesU,map_mul,RingHom.map_rat_algebraMap,InfinityCharacterUnits318.indexedRatio_embedding,
    InfinityOrderCoordinates318.coordinate_embedding]
  change algebraMap ℚ L (units 0:ℚ)*(_/_)=
    (algebraMap ℚ L (units 0:ℚ)/InfinityFieldCoordinates318.root units 0)*_
  ring
lemma fifth_common:
    AlgHomDifferential318.map lift FifthInfinityInvariantCoefficient318.pulled=
      FifthOverlapDifferentialEquation318.pulled:=by
  have h:lift.comp FifthSourceInfinityAlgebra318.shortMap=FifthSourceOverlap318.shortMap:=by
    apply AlgHom.ext
    intro a
    exact (RingHom.congr_fun FifthGlobalCompatibility318.short_maps_agree a).symm
  change AlgHomDifferential318.map lift
    (AlgHomDifferential318.map FifthSourceInfinityAlgebra318.shortMap _)=_
  rw [←DifferentialFunctor318.map_comp_apply,h]
  rfl
/-- The exact coefficient, expressed using already normalized fifth-map
coordinates. All factors are units, including at u=0. -/
@[expose] def coefficient (i:Fin 4):I:=
  algebraMap ℚ I (CharacterFifthCommonMultiple318.factor i)*rootTimesU i*
    FifthInfinityInvariantCoefficient318.factor
lemma coefficient_unit (i:Fin 4):IsUnit (coefficient i):=
  (((CharacterFifthCommonMultiple318.factor_unit i).map (algebraMap ℚ I)).mul
    (rootTimesU_unit i)).mul FifthInfinityInvariantCoefficient318.factor_unit
@[expose] def form (i:Fin 4):KaehlerDifferential ℚ I:=coefficient i • KaehlerDifferential.D ℚ I u
lemma frame_value (i:Fin 4):ContactDifferentialFrames318.infinityFrame units (form i)=coefficient i:=by
  have h:ContactDifferentialFrames318.infinityFrame units (KaehlerDifferential.D ℚ I u)=1:=
    InfinityDifferentialDivisibility318.coordinate_normalized units
  rw [form,map_smul,smul_eq_mul,h,mul_one]
/-- The whole infinity form matches the original complementary pullback
on the entire common open. No inverse of u is used in the infinity ring. -/
theorem common_eq (i:Fin 4):AlgHomDifferential318.map lift (form i)=FifthFormCommonOpen318.form i:=by
  rw [CharacterFifthCommonMultiple318.form_eq,←fifth_common,
    FifthInfinityInvariantCoefficient318.normalized,AlgHomDifferential318.map_smul,
    form,AlgHomDifferential318.map_smul]
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  simp only [map_smul,smul_eq_mul]
  rw [coefficient,map_mul,map_mul,AlgHom.commutes,root_relation,map_mul]
  ring
end CharacterInfinityLocalForm318
