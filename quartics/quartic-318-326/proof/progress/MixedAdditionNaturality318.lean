module
public import MixedAdditionGluing318
public section
noncomputable section
namespace MixedAdditionNaturality318
open AlgebraicGeometry CategoryTheory
open InfinityInputAlgebra318
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
@[expose] def finiteLift (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    MixedInputLocal318.FiniteRing A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=f) (v A B) hv
@[simp] theorem finiteLift_pair (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (r:PairRing A B) : finiteLift A B f hv (MixedInputLocal318.finiteInput A B r)=f r := by
  simp only [finiteLift,MixedInputLocal318.finiteInput,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl
lemma finiteLift_pairMap (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    (finiteLift A B f hv).comp (MixedInputLocal318.finitePair A B)=MixedFiniteInput318.finitePair A B f hv := by
  have he:(finiteLift A B f hv).comp (MixedInputLocal318.finiteInput A B)=f := by
    apply AlgHom.ext
    exact finiteLift_pair A B f hv
  unfold MixedInputLocal318.finitePair
  rw [MixedFiniteInput318.finitePair_natural]
  simp only [he]

/-- The whole mixed law restricts to the whole finite law under every finite
first-input extraction, as an actual Scheme-morphism equality. -/
theorem finite_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ MixedAdditionGluing318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom (MixedFiniteInput318.finitePair A B f hv).toRingHom) ≫
        FiniteAdditionGluing318.coordinateAddition A B hD := by
  have hf:Spec.map (CommRingCat.ofHom (finiteLift A B f hv).toRingHom) ≫
      (InfinityInputCover318.coordinateCover A B).f (0:Fin 2)=Spec.map (CommRingCat.ofHom f.toRingHom) := by
    change Spec.map (CommRingCat.ofHom (finiteLift A B f hv).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (MixedInputLocal318.FiniteRing A B)))=_
    rw [←Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (finiteLift_pair A B f hv))
  rw [←hf,Category.assoc,MixedAdditionGluing318.coordinate_restriction]
  change Spec.map (CommRingCat.ofHom (finiteLift A B f hv).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (MixedInputLocal318.finitePair A B).toRingHom) ≫
      FiniteAdditionGluing318.coordinateAddition A B hD)=_
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact AlgHom.congr_fun (finiteLift_pairMap A B f hv) r

/-- The other mixed-cover restriction, over an arbitrary coefficient algebra. -/
theorem regular_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:OutputRing A B →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (f.comp (pairMap A B)).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ InfinityInputScheme318.addition A B := by
  have hh:=congrArg (fun g => Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g)
    (MixedAdditionGluing318.coordinate_restriction A B hD (1:Fin 2))
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (OutputRing A B))) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=_ at hh
  rw [←Category.assoc,←Spec.map_comp] at hh
  exact hh
end MixedAdditionNaturality318
