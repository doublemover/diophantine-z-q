module
public import InfinityBoundaryDoubling318
public import CompletedAdditionRestrictions318
public import CompletedIteratedAddition318
public import GluedNegation318
import all WeierstrassGluing318
public section
noncomputable section
namespace InfinityBoundaryScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityBoundaryDoubling318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A B:R) (f:InfinityChart318.Ring A B →ₐ[R] S)
variable (hz:f (InfinityChart318.z A B)=0)

@[expose] def chartPoint : Spec (CommRingCat.of S) ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom f.toRingHom)
@[expose] def point : Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  chartPoint A B f ≫ WeierstrassGluing318.infinityChart A B
@[expose] def regularPoint : Spec (CommRingCat.of S) ⟶ BothInfinityScheme318.domain A B :=
  Spec.map (CommRingCat.ofHom (InfinityBoundaryDoubling318.lift A B f hz).toRingHom)

lemma point_over_base : point A B f ≫ WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [point,Category.assoc,WeierstrassGluing318.infinityChart_structure]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (InfinityChart318.Ring A B)))=_
  rw [←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

lemma point_origin : point A B ((Algebra.ofId R S).comp (InfinityChart318.origin A B))=
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ WeierstrassGluing318.infinity A B := by
  change Spec.map (CommRingCat.ofHom ((Algebra.ofId R S).comp (InfinityChart318.origin A B)).toRingHom) ≫
    WeierstrassGluing318.infinityChart A B=
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
      (Spec.map (CommRingCat.ofHom (InfinityChart318.origin A B).toRingHom) ≫ WeierstrassGluing318.infinityChart A B)
  rw [←Category.assoc,←Spec.map_comp]
  rfl

lemma point_eq_zero_iff : point A B f=
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ WeierstrassGluing318.infinity A B ↔
      f=(Algebra.ofId R S).comp (InfinityChart318.origin A B) := by
  rw [←point_origin A B]
  constructor
  · intro h
    exact ChartInputEquality318.infinity_injective A B _ _ h
  · rintro rfl
    rfl

lemma lift_left : (InfinityBoundaryDoubling318.lift A B f hz).comp
    (BothInfinityScheme318.leftInput A B)=f := by
  apply AlgHom.ext
  intro a
  change InfinityBoundaryDoubling318.lift A B f hz
    (BothInfinityAlgebra318.pairMap A B (BothInfinityAlgebra318.leftPair A B a))=f a
  rw [InfinityBoundaryDoubling318.lift_pair,InfinityBoundaryDoubling318.pair_left]
lemma lift_right : (InfinityBoundaryDoubling318.lift A B f hz).comp
    (BothInfinityScheme318.rightInput A B)=f := by
  apply AlgHom.ext
  intro a
  change InfinityBoundaryDoubling318.lift A B f hz
    (BothInfinityAlgebra318.pairMap A B (BothInfinityAlgebra318.rightPair A B a))=f a
  rw [InfinityBoundaryDoubling318.lift_pair,InfinityBoundaryDoubling318.pair_right]

lemma regular_fst : regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.fst _ _=
    chartPoint A B f := by
  rw [BothInfinityScheme318.intoProduct_fst]
  change Spec.map (CommRingCat.ofHom (InfinityBoundaryDoubling318.lift A B f hz).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.leftInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((InfinityBoundaryDoubling318.lift A B f hz).comp
    (BothInfinityScheme318.leftInput A B)).toRingHom)=_
  rw [lift_left]
  rfl
lemma regular_snd : regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.snd _ _=
    chartPoint A B f := by
  rw [BothInfinityScheme318.intoProduct_snd]
  change Spec.map (CommRingCat.ofHom (InfinityBoundaryDoubling318.lift A B f hz).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.rightInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((InfinityBoundaryDoubling318.lift A B f hz).comp
    (BothInfinityScheme318.rightInput A B)).toRingHom)=_
  rw [lift_right]
  rfl

lemma diagonal_input : regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫
    CompletedAdditionRestrictions318.inputChart A B 1 1=
      point A B f ≫ CompletedIteratedAddition318.diagonal A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_fst,
      CompletedIteratedAddition318.diagonal_fst,Category.comp_id]
    change regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫
      pullback.fst _ _ ≫ WeierstrassGluing318.infinityChart A B=point A B f
    simpa only [point,Category.assoc] using congrArg
      (fun k=>k ≫ WeierstrassGluing318.infinityChart A B) (regular_fst A B f hz)
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_snd,
      CompletedIteratedAddition318.diagonal_snd,Category.comp_id]
    change regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫
      pullback.snd _ _ ≫ WeierstrassGluing318.infinityChart A B=point A B f
    simpa only [point,Category.assoc] using congrArg
      (fun k=>k ≫ WeierstrassGluing318.infinityChart A B) (regular_snd A B f hz)

lemma doubling (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    point A B f ≫ CompletedIteratedAddition318.doubling A B hD=
      Spec.map (CommRingCat.ofHom ((InfinityBoundaryDoubling318.lift A B f hz).comp
        (BothInfinityAlgebra318.outputMap A B)).toRingHom) ≫ WeierstrassGluing318.infinityChart A B := by
  rw [CompletedIteratedAddition318.doubling,←Category.assoc,←diagonal_input,Category.assoc,Category.assoc,
    CompletedAdditionRestrictions318.inputChart_addition]
  change regularPoint A B f hz ≫ BothInfinityScheme318.intoProduct A B ≫
    WholeBothInfinity318.addition A B hD=_
  rw [WholeBothInfinity318.regular_restriction]
  change Spec.map (CommRingCat.ofHom (InfinityBoundaryDoubling318.lift A B f hz).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInfinityAlgebra318.outputMap A B).toRingHom) ≫ _)=_
  rw [←Category.assoc,←Spec.map_comp]
  rfl

lemma negation : point A B f ≫ GluedNegation318.negation A B=
    Spec.map (CommRingCat.ofHom (f.comp (ChartNegation318.infinityNeg A B)).toRingHom) ≫
      WeierstrassGluing318.infinityChart A B := by
  rw [point,Category.assoc,GluedNegation318.infinityChart_negation,←Category.assoc]
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ChartNegation318.infinityNeg A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl

include hz in
/-- The actual completed doubling/negation equalizer on the z=0 chart boundary
is the actual origin, tested over every coefficient algebra including nilpotents. -/
theorem double_neg_iff (hD:IsUnit (-16*(4*A^3+27*B^2))) (h3:IsUnit (3:S)) :
    point A B f ≫ CompletedIteratedAddition318.doubling A B hD=point A B f ≫ GluedNegation318.negation A B ↔
      f=(Algebra.ofId R S).comp (InfinityChart318.origin A B) := by
  rw [doubling A B f hz hD,negation]
  rw [cancel_mono]
  constructor
  · intro h
    apply (InfinityBoundaryDoubling318.double_neg_iff A B f hz h3).mp
    apply AlgHom.ext
    intro a
    exact congrArg (fun k=>k.hom a) (Spec.map_injective h)
  · intro h
    rw [(InfinityBoundaryDoubling318.double_neg_iff A B f hz h3).mpr h]
end InfinityBoundaryScheme318
