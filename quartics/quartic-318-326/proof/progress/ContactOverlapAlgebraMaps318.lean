module
public import BranchFullOverlap318
public import ContactBicanonicalCoefficients318
public section
noncomputable section
namespace ContactOverlapAlgebraMaps318
open Polynomial CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev Source:=ContactKummerOrder318.OpenOrder c
abbrev Infinity:=InfinityOpenChart318.OpenOrder c
abbrev Branch (i:Fin 4):=BranchOverlapLocalization318.Branch c i

/-- The exact infinity restriction as a Q-algebra map for universal differentials. -/
@[expose] def infinityMap : Infinity c→ₐ[ℚ]Source c where
  __ := InfinityOverlapLocalization318.toOpen c
  commutes' := RingHom.map_rat_algebraMap _

/-- The exact finite-branch restriction as a Q-algebra map, for every branch. -/
@[expose] def branchMap (i:Fin 4):Branch c i→ₐ[ℚ]Source c where
  __ := BranchOverlapLocalization318.toOpen c i
  commutes' := RingHom.map_rat_algebraMap _

theorem infinityMap_coordinate : infinityMap c (ContactFrameNormalization318.infinityCoordinate c)=
    SourceInfinityOverlap318.u c:=rfl

theorem branchMap_coordinate (i:Fin 4):branchMap c i (ContactBicanonicalCoefficients318.branchT c i)=
    SourceInfinityOverlap318.t c:=by
  change BranchOverlapLocalization318.toOpen c i
    (algebraMap (ContactKummerOrder318.SourceOrder c) (Branch c i)
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) X))=_
  rw [BranchOverlapLocalization318.toOpen_on_source,SourceOpenFractionField318.orderToOpen_on_polynomial]
  rfl

theorem actual_coordinate_relation :
    (infinityMap c (ContactFrameNormalization318.infinityCoordinate c))^2*
      SourceInfinityOverlap318.t c=algebraMap ℚ (Source c) (c 0:ℚ):=
  SourceInfinityOverlap318.coordinate_relation c

theorem maps_agree (i:Fin 4):
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (branchMap c i).toRingHom)≫
      ContactIntrinsicFrames318.branchEmbedding c i=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (infinityMap c).toRingHom)≫
      InfinityGlobalScheme318.chartEmbedding c:=
  BranchFullOverlap318.maps_agree c i
end ContactOverlapAlgebraMaps318
