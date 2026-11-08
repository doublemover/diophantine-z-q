module
public import InfinityKernelNeighborhoodOrigin318
public import CompletedAdditionRestrictions318
public import CompletedIteratedAddition318
public import AffineProductEvaluation318
public import SchemeAffineTestExt318
public import GluedNegation318
public section
noncomputable section
namespace InfinityKernelNeighborhoodScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityKernelNeighborhoodAlgebra318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R] (A B:R)
@[expose] def scheme : Scheme := Spec (CommRingCat.of (Ring A B))
@[expose] def chartPoint : scheme A B ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (input A B).toRingHom)
@[expose] def intoCurve : scheme A B ⟶ WeierstrassGluing318.scheme A B :=
  chartPoint A B ≫ WeierstrassGluing318.infinityChart A B
@[expose] def structureMap : scheme A B ⟶ Spec (CommRingCat.of R) :=
  intoCurve A B ≫ WeierstrassGluing318.structureMap A B
@[expose] def regularPoint : scheme A B ⟶ BothInfinityScheme318.domain A B :=
  Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodAlgebra318.lift A B).toRingHom)

instance chartPoint_open : IsOpenImmersion (chartPoint A B) := by
  exact IsOpenImmersion.of_isLocalization (S:=Ring A B) (denominator A B)
instance intoCurve_open : IsOpenImmersion (intoCurve A B) := by
  dsimp only [intoCurve]
  infer_instance
lemma lift_left : (InfinityKernelNeighborhoodAlgebra318.lift A B).comp
    (BothInfinityScheme318.leftInput A B)=input A B := by
  apply AlgHom.ext
  intro a
  change InfinityKernelNeighborhoodAlgebra318.lift A B
    (BothInfinityAlgebra318.pairMap A B (BothInfinityAlgebra318.leftPair A B a))=input A B a
  rw [InfinityKernelNeighborhoodAlgebra318.lift_pair,InfinityKernelNeighborhoodAlgebra318.pair_left]
lemma lift_right : (InfinityKernelNeighborhoodAlgebra318.lift A B).comp
    (BothInfinityScheme318.rightInput A B)=input A B := by
  apply AlgHom.ext
  intro a
  change InfinityKernelNeighborhoodAlgebra318.lift A B
    (BothInfinityAlgebra318.pairMap A B (BothInfinityAlgebra318.rightPair A B a))=input A B a
  rw [InfinityKernelNeighborhoodAlgebra318.lift_pair,InfinityKernelNeighborhoodAlgebra318.pair_right]

lemma regular_fst : regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.fst _ _=
    chartPoint A B := by
  rw [BothInfinityScheme318.intoProduct_fst]
  change Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodAlgebra318.lift A B).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.leftInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((InfinityKernelNeighborhoodAlgebra318.lift A B).comp
    (BothInfinityScheme318.leftInput A B)).toRingHom)=_
  rw [lift_left]
  rfl
lemma regular_snd : regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫ pullback.snd _ _=
    chartPoint A B := by
  rw [BothInfinityScheme318.intoProduct_snd]
  change Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodAlgebra318.lift A B).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (BothInfinityScheme318.rightInput A B).toRingHom)=_
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((InfinityKernelNeighborhoodAlgebra318.lift A B).comp
    (BothInfinityScheme318.rightInput A B)).toRingHom)=_
  rw [lift_right]
  rfl

lemma diagonal_input : regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫
    CompletedAdditionRestrictions318.inputChart A B 1 1=
      intoCurve A B ≫ CompletedIteratedAddition318.diagonal A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_fst,
      CompletedIteratedAddition318.diagonal_fst,Category.comp_id]
    change regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫
      pullback.fst _ _ ≫ WeierstrassGluing318.infinityChart A B=intoCurve A B
    simpa only [intoCurve,Category.assoc] using congrArg
      (fun k=>k ≫ WeierstrassGluing318.infinityChart A B) (regular_fst A B)
  · simp only [Category.assoc,CompletedAdditionRestrictions318.inputChart_snd,
      CompletedIteratedAddition318.diagonal_snd,Category.comp_id]
    change regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫
      pullback.snd _ _ ≫ WeierstrassGluing318.infinityChart A B=intoCurve A B
    simpa only [intoCurve,Category.assoc] using congrArg
      (fun k=>k ≫ WeierstrassGluing318.infinityChart A B) (regular_snd A B)

lemma doubling (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    intoCurve A B ≫ CompletedIteratedAddition318.doubling A B hD=
      Spec.map (CommRingCat.ofHom ((InfinityKernelNeighborhoodAlgebra318.lift A B).comp
        (BothInfinityAlgebra318.outputMap A B)).toRingHom) ≫ WeierstrassGluing318.infinityChart A B := by
  rw [CompletedIteratedAddition318.doubling,←Category.assoc,←diagonal_input,Category.assoc,Category.assoc,
    CompletedAdditionRestrictions318.inputChart_addition]
  change regularPoint A B ≫ BothInfinityScheme318.intoProduct A B ≫
    WholeBothInfinity318.addition A B hD=_
  rw [WholeBothInfinity318.regular_restriction]
  change Spec.map (CommRingCat.ofHom (InfinityKernelNeighborhoodAlgebra318.lift A B).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInfinityAlgebra318.outputMap A B).toRingHom) ≫ _)=_
  rw [←Category.assoc,←Spec.map_comp]
  rfl

lemma negation : intoCurve A B ≫ GluedNegation318.negation A B=
    Spec.map (CommRingCat.ofHom ((input A B).comp (ChartNegation318.infinityNeg A B)).toRingHom) ≫
      WeierstrassGluing318.infinityChart A B := by
  rw [intoCurve,Category.assoc,GluedNegation318.infinityChart_negation,←Category.assoc]
  change (Spec.map (CommRingCat.ofHom (input A B).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ChartNegation318.infinityNeg A B).toRingHom)) ≫ _=_
  rw [←Spec.map_comp]
  rfl


end InfinityKernelNeighborhoodScheme318
