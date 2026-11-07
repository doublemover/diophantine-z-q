module
public import FiniteAdditionLocal318
public section
noncomputable section
namespace FiniteAdditionGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open FinitePairCover318 FinitePairSchemeCover318 FiniteAdditionLocal318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R]

/-- Compatibility on the actual categorical pullbacks, derived from tensor-product maps. -/
theorem coordinate_compatibility (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 4) :
    pullback.fst ((coordinateCover A B hD).f i) ((coordinateCover A B hD).f j) ≫ localAddition A B i=
      pullback.snd _ _ ≫ localAddition A B j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i))))
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B j)))) ≫ localAddition A B i=
    pullback.snd _ _ ≫ localAddition A B j
  apply (cancel_epi (pullbackSpecIso (PairRing A B) (LocalRing A B i) (LocalRing A B j)).inv).mp
  rw [←Category.assoc,pullbackSpecIso_inv_fst,←Category.assoc,pullbackSpecIso_inv_snd]
  exact local_agreement A B i j (left A B i j) (right A B i j) (same_pair A B i j)

/-- Actual addition on the entire finite-input tensor scheme, not a rational map. -/
@[expose] def coordinateAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec (CommRingCat.of (PairRing A B)) ⟶ WeierstrassGluing318.scheme A B :=
  (coordinateCover A B hD).glueMorphisms (fun i=>localAddition A B i)
    (coordinate_compatibility A B hD)

theorem coordinate_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 4) :
    (coordinateCover A B hD).f i ≫ coordinateAddition A B hD=localAddition A B i :=
  (coordinateCover A B hD).ι_glueMorphisms _ _ i

/-- Actual global morphism for every pair of finite inputs into the completed curve. -/
@[expose] def addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    RelativeChordScheme318.productScheme A B ⟶ WeierstrassGluing318.scheme A B :=
  (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫
    coordinateAddition A B hD

/-- It restricts to each of the four genuine existing addition morphisms. -/
theorem restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 4) :
    (productCover A B hD).f i ≫ addition A B hD=localAddition A B i := by
  change ((coordinateCover A B hD).f i ≫
      (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv) ≫
      ((pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫
      coordinateAddition A B hD)=_
  rw [Category.assoc,Iso.inv_hom_id_assoc,coordinate_restriction]

/-- The glued map preserves the original coefficient base. -/
theorem coordinate_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    coordinateAddition A B hD ≫ WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B))) := by
  apply (coordinateCover A B hD).hom_ext
  intro i
  rw [←Category.assoc,coordinate_restriction,local_over_base]
  change Spec.map (CommRingCat.ofHom (algebraMap R (LocalRing A B i)))=
      Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B)))
  rw [←Spec.map_comp]
  congr 1

/-- The actual finite-input addition is a morphism over the original base. -/
theorem addition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    addition A B hD ≫ WeierstrassGluing318.structureMap A B=
      pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        ShortAffineScheme318.structureMap A B := by
  rw [addition,Category.assoc,coordinate_over_base]
  dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
  apply (cancel_epi (pullbackSpecIso R (ShortAffineJacobian318.Ring A B)
    (ShortAffineJacobian318.Ring A B)).inv).mp
  rw [Iso.inv_hom_id_assoc,←Category.assoc,pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B)))=
    Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.leftPair A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ShortAffineJacobian318.Ring A B)))
  rw [←Spec.map_comp]
  congr 1

@[expose] def literalAddition (N:ℕ) :
    RelativeChordScheme318.productScheme (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ⟶
      WeierstrassGluing318.literalScheme N :=
  addition _ _ (OpenJAffineScheme318.discriminant_unit N)

end FiniteAdditionGluing318
