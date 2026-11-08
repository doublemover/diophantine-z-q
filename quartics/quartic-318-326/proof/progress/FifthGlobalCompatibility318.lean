module
public import FifthSourceOverlap318
public import FifthSourceInfinityScheme318
public import ContactFullOverlap318
public section
noncomputable section
namespace FifthGlobalCompatibility318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 700000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Both whole source charts restrict to the very same coordinate homomorphism
on their actual full intersection, inside the original function field. -/
theorem short_maps_agree:
    FifthSourceOverlap318.shortMap.toRingHom=
      (InfinityOverlapLocalization318.toOpen units).comp FifthSourceInfinityAlgebra318.shortMap.toRingHom:=by
  apply RingHom.ext
  intro x
  apply SourceOpenFractionField318.openEmbedding_injective units
  change SourceOpenFractionField318.openEmbedding units (FifthSourceOverlap318.shortMap x)=
    SourceOpenFractionField318.openEmbedding units
      (InfinityOverlapLocalization318.toOpen units (FifthSourceInfinityAlgebra318.shortMap x))
  rw [FifthSourceOverlap318.shortMap_raw]
  change (FifthShortFraction318.embedding x:FifthCharacterField318.L)=
    SourceOpenFractionField318.openEmbedding units
      (InfinityOverlapLocalization318.toOpen units (FifthSourceInfinityAlgebra318.shortMap x))
  rw [InfinityOverlapLocalization318.toOpen_embedding]
  exact (RingHom.congr_fun FifthSourceInfinityAlgebra318.original_field_square x).symm
@[reassoc] theorem maps_agree:
    ContactOverlapMaps318.sourceInclusion units≫FifthQuarticCompletedMap318.sourceMap=
      ContactOverlapMaps318.infinityInclusion units≫FifthSourceInfinityScheme318.intoCompleted:=by
  rw [FifthSourceOverlap318.finite_restriction]
  change Spec.map (CommRingCat.ofHom FifthSourceOverlap318.shortMap.toRingHom)≫
      WeierstrassGluing318.finiteChart A B=
    Spec.map (CommRingCat.ofHom (InfinityOverlapLocalization318.toOpen units))≫
      (Spec.map (CommRingCat.ofHom FifthSourceInfinityAlgebra318.shortMap.toRingHom)≫
        WeierstrassGluing318.finiteChart A B)
  rw [←Category.assoc,←Spec.map_comp,short_maps_agree]
  rfl
end FifthGlobalCompatibility318
