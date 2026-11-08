module
public import WholeBothInfinity318
public section
noncomputable section
namespace WholeBothNaturality318
open AlgebraicGeometry CategoryTheory
open BothInfinityAlgebra318 BothInfinityLocal318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
@[expose] def localLift (A B:R) (i:Fin 3) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (BothInfinityCover318.chartElement A B i))) : LocalRing A B i →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=f) (BothInfinityCover318.chartElement A B i) h
@[simp] theorem localLift_input (A B:R) (i:Fin 3) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (BothInfinityCover318.chartElement A B i))) (r:PairRing A B) :
    localLift A B i f h (inputMap A B i r)=f r := by
  simp only [localLift,inputMap,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl
lemma localLift_comp (A B:R) (i:Fin 3) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (BothInfinityCover318.chartElement A B i))) :
    (localLift A B i f h).comp (inputMap A B i)=f :=
  AlgHom.ext (localLift_input A B i f h)

/-- Restriction of the entire infinity-product law to any coefficient algebra
whose chosen chart denominator is a unit. -/
theorem restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (i:Fin 3) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (BothInfinityCover318.chartElement A B i))) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WholeBothInfinity318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom (localLift A B i f h).toRingHom) ≫ localAddition A B hD i := by
  have hf:Spec.map (CommRingCat.ofHom (localLift A B i f h).toRingHom) ≫
      (WholeBothInfinity318.coordinateCover A B).f i=Spec.map (CommRingCat.ofHom f.toRingHom) := by
    change Spec.map (CommRingCat.ofHom (localLift A B i f h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i)))=_
    rw [←Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (localLift_input A B i f h))
  rw [←hf,Category.assoc,WholeBothInfinity318.coordinate_restriction]

theorem right_finite (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WholeBothInfinity318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B f h).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD := by
  rw [restriction A B hD 1 f h]
  change Spec.map (CommRingCat.ofHom (localLift A B 1 f h).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=_
  rw [←Category.assoc,SpecAlgHomComposition318.map_comp]
  simp only [BothInputExtraction318.mixedPair_natural,localLift_comp]

theorem left_finite (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V1 A B))) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WholeBothInfinity318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B f h).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD := by
  rw [restriction A B hD 0 f h]
  change Spec.map (CommRingCat.ofHom (localLift A B 0 f h).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=_
  rw [←Category.assoc,SpecAlgHomComposition318.map_comp]
  simp only [BothInputSwap318.mixedLeft_natural,localLift_comp]
end WholeBothNaturality318
