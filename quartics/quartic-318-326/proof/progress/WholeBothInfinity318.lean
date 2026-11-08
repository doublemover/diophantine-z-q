module
public import BothInfinityLocal318
public import BothInfinityOrigin318
public section
noncomputable section
namespace WholeBothInfinity318
open BothInfinityAlgebra318 BothInfinityLocal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def coordinateCover (A B:R) : (Spec (CommRingCat.of (PairRing A B))).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (PairRing A B))
    (BothInfinityCover318.chartElement A B) (BothInfinityCover318.chart_span_top A B)).openCover

theorem coordinate_compatibility (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 3) :
    pullback.fst ((coordinateCover A B).f i) ((coordinateCover A B).f j) ≫ localAddition A B hD i=
      pullback.snd _ _ ≫ localAddition A B hD j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i))))
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B j)))) ≫ localAddition A B hD i=
    pullback.snd _ _ ≫ localAddition A B hD j
  apply (cancel_epi (pullbackSpecIso (PairRing A B) (LocalRing A B i) (LocalRing A B j)).inv).mp
  rw [←Category.assoc,pullbackSpecIso_inv_fst,←Category.assoc,pullbackSpecIso_inv_snd]
  exact local_agreement A B hD i j

/-- The actual addition morphism on the entire infinity-chart input product,
glued on the two finite-transition opens and the regular both-infinity open. -/
@[expose] def coordinateAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec (CommRingCat.of (PairRing A B)) ⟶ WeierstrassGluing318.scheme A B :=
  (coordinateCover A B).glueMorphisms (localAddition A B hD) (coordinate_compatibility A B hD)
theorem coordinate_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 3) :
    (coordinateCover A B).f i ≫ coordinateAddition A B hD=localAddition A B hD i :=
  (coordinateCover A B).ι_glueMorphisms _ _ i
@[expose] def addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    BothInfinityScheme318.productScheme A B ⟶ WeierstrassGluing318.scheme A B :=
  (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).hom ≫ coordinateAddition A B hD

theorem restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 3) :
    (BothInfinityCover318.productCover A B).f i ≫ addition A B hD=localAddition A B hD i := by
  change ((coordinateCover A B).f i ≫
      (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).inv) ≫
      ((pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).hom ≫
      coordinateAddition A B hD)=_
  rw [Category.assoc,Iso.inv_hom_id_assoc,coordinate_restriction]

theorem regular_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    BothInfinityScheme318.intoProduct A B ≫ addition A B hD=BothInfinityScheme318.addition A B :=
  restriction A B hD 2

lemma local_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 3) :
    localAddition A B hD i ≫ WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (LocalRing A B i))) := by
  fin_cases i
  · change (Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD) ≫ _=_
    rw [Category.assoc,MixedAdditionGluing318.coordinate_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).comp_algebraMap
  · change (Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD) ≫ _=_
    rw [Category.assoc,MixedAdditionGluing318.coordinate_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).comp_algebraMap
  · exact BothInfinityScheme318.addition_over_base A B

theorem coordinate_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    coordinateAddition A B hD ≫ WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B))) := by
  apply (coordinateCover A B).hom_ext
  intro i
  rw [←Category.assoc,coordinate_restriction,local_over_base]
  change Spec.map (CommRingCat.ofHom (algebraMap R (LocalRing A B i)))=
      Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B)))
  rw [←Spec.map_comp]
  congr 1

theorem addition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    addition A B hD ≫ WeierstrassGluing318.structureMap A B=
      pullback.fst (InfinitySmooth318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        InfinitySmooth318.structureMap A B := by
  rw [addition,Category.assoc,coordinate_over_base]
  dsimp only [InfinitySmooth318.structureMap,InfinitySmooth318.scheme]
  apply (cancel_epi (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).inv).mp
  rw [Iso.inv_hom_id_assoc,←Category.assoc,pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B)))=
    Spec.map (CommRingCat.ofHom (leftPair A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityChart318.Ring A B)))
  rw [←Spec.map_comp]
  congr 1

/-- The glued morphism sends the actual pair of infinity sections to infinity. -/
theorem origin_output (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    BothInfinityOrigin318.originSection A B ≫ BothInfinityScheme318.intoProduct A B ≫ addition A B hD=
      WeierstrassGluing318.infinity A B := by
  rw [regular_restriction]
  exact BothInfinityOrigin318.section_output A B
@[expose] def literalAddition (N:ℕ) :=
  addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
end WholeBothInfinity318
