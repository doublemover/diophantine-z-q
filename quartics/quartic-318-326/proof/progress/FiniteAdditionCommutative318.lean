module
public import FiniteLocalSymmetry318
public import FiniteAdditionGluing318
public section
noncomputable section
namespace FiniteAdditionCommutative318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteAdditionLocal318 FinitePairSchemeCover318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

@[expose] def localSwap (A B:R) (i:Fin 4) : LocalRing A B i →ₐ[R] LocalRing A B i :=
  IsLocalization.Away.liftAlgHom (f:=(inputMap A B i).comp (FinitePairSwap318.swap A B))
    (FinitePairCover318.chartElement A B i)
    (FinitePairSwap318.chartElement_unit A B (inputMap A B i) i
      (IsLocalization.Away.algebraMap_isUnit (S:=LocalRing A B i) (FinitePairCover318.chartElement A B i)))
@[simp] theorem localSwap_pair (A B:R) (i:Fin 4) (r:RelativeChordAlgebra318.PairRing A B) :
    localSwap A B i (inputMap A B i r)=inputMap A B i (FinitePairSwap318.swap A B r) := by
  simp only [localSwap,inputMap,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq,AlgHom.comp_apply]
  rfl

/-- Actual invariance on each of the four addition domains. -/
theorem local_commutative (A B:R) (i:Fin 4) :
    Spec.map (CommRingCat.ofHom (localSwap A B i).toRingHom) ≫ localAddition A B i=
      localAddition A B i := by
  have hh := FiniteLocalSymmetry318.scheme_agreement A B i (localSwap A B i)
    (AlgHom.id R (LocalRing A B i)) (localSwap_pair A B i)
  have hid : CommRingCat.ofHom (AlgHom.id R (LocalRing A B i)).toRingHom=𝟙 (CommRingCat.of (LocalRing A B i)) := rfl
  rw [hid,Spec.map_id,Category.id_comp] at hh
  exact hh

/-- Commutativity of the actual whole finite-input addition morphism. -/
theorem coordinate_commutative (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec.map (CommRingCat.ofHom (FinitePairSwap318.swap A B).toRingHom) ≫
        FiniteAdditionGluing318.coordinateAddition A B hD=
      FiniteAdditionGluing318.coordinateAddition A B hD := by
  apply (coordinateCover A B hD).hom_ext
  intro i
  have hp : (coordinateCover A B hD).f i ≫
      Spec.map (CommRingCat.ofHom (FinitePairSwap318.swap A B).toRingHom)=
      Spec.map (CommRingCat.ofHom (localSwap A B i).toRingHom) ≫ (coordinateCover A B hD).f i := by
    change Spec.map (CommRingCat.ofHom (algebraMap (RelativeChordAlgebra318.PairRing A B) (LocalRing A B i))) ≫
      Spec.map (CommRingCat.ofHom (FinitePairSwap318.swap A B).toRingHom)=
      Spec.map (CommRingCat.ofHom (localSwap A B i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (RelativeChordAlgebra318.PairRing A B) (LocalRing A B i)))
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (fun r => (localSwap_pair A B i r).symm))
  rw [←Category.assoc,hp,Category.assoc,FiniteAdditionGluing318.coordinate_restriction,local_commutative]
end FiniteAdditionCommutative318
