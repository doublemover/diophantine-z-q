module
public import FiniteCoefficientNaturality318
public import CompletedAdditionCommutative318
public section
noncomputable section
namespace CompletedCoefficientProduct318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassGluing318 WeierstrassCoefficientMap318
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S
@[expose] def finitePair (A B:R) : RelativeChordScheme318.productScheme (a A) (a B) ⟶ RelativeChordScheme318.productScheme A B :=
  pullback.lift (pullback.fst _ _ ≫ finiteMap A B) (pullback.snd _ _ ≫ finiteMap A B) (by
    rw [Category.assoc,finiteMap_base,←Category.assoc,pullback.condition,Category.assoc,←finiteMap_base,←Category.assoc])
@[reassoc] theorem finitePair_fst (A B:R) : finitePair (S:=S) A B ≫ pullback.fst _ _=pullback.fst _ _ ≫ finiteMap A B := by simp [finitePair]
@[reassoc] theorem finitePair_snd (A B:R) : finitePair (S:=S) A B ≫ pullback.snd _ _=pullback.snd _ _ ≫ finiteMap A B := by simp [finitePair]
@[expose] def pair (A B:R) : pullback (structureMap (a A) (a B)) (structureMap (a A) (a B)) ⟶
    pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (pullback.fst _ _ ≫ coefficientMap A B) (pullback.snd _ _ ≫ coefficientMap A B) (by
    rw [Category.assoc,coefficientMap_base,←Category.assoc,pullback.condition,Category.assoc,←coefficientMap_base,←Category.assoc])
@[reassoc] theorem pair_fst (A B:R) : pair (S:=S) A B ≫ pullback.fst _ _=pullback.fst _ _ ≫ coefficientMap A B := by simp [pair]
@[reassoc] theorem pair_snd (A B:R) : pair (S:=S) A B ≫ pullback.snd _ _=pullback.snd _ _ ≫ coefficientMap A B := by simp [pair]

theorem tensor_pair (A B:R) :
    (pullbackSpecIso S (ShortAffineJacobian318.Ring (a A) (a B)) (ShortAffineJacobian318.Ring (a A) (a B))).inv ≫ finitePair A B=
    Spec.map (CommRingCat.ofHom (FinitePairCoefficient318.pair (S:=S) A B).toRingHom) ≫
      (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc,finitePair_fst]
    dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
    rw [←Category.assoc,pullbackSpecIso_inv_fst,Category.assoc,pullbackSpecIso_inv_fst]
    unfold finiteMap
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (FinitePairCoefficient318.pair_left A B x).symm
  · rw [Category.assoc,finitePair_snd]
    dsimp only [ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
    rw [←Category.assoc,pullbackSpecIso_inv_snd,Category.assoc,pullbackSpecIso_inv_snd]
    unfold finiteMap
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (FinitePairCoefficient318.pair_right A B x).symm

theorem finite_pair (A B:R) :
    FiniteProductSchematicDensity318.pairMap (a A) (a B) ≫ pair (S:=S) A B=
      finitePair A B ≫ FiniteProductSchematicDensity318.pairMap A B := by
  apply pullback.hom_ext
  · simp only [Category.assoc,pair_fst,FiniteProductSchematicDensity318.pairMap_fst,
      FiniteProductSchematicDensity318.pairMap_fst_assoc,finite_coefficientMap,finitePair_fst_assoc]
  · simp only [Category.assoc,pair_snd,FiniteProductSchematicDensity318.pairMap_snd,
      FiniteProductSchematicDensity318.pairMap_snd_assoc,finite_coefficientMap,finitePair_snd_assoc]

theorem finite_restriction {T:Type u} [CommRing T] (A B:T) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    FiniteProductSchematicDensity318.pairMap A B ≫ CompletedAddition318.addition A B hD=
      FiniteAdditionGluing318.addition A B hD := by
  rw [←CompletedAdditionCommutative318.inputChart_eq_pairMap,CompletedAdditionRestrictions318.inputChart_addition]
  rfl

theorem finite_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (hS:IsUnit (-16*(4*(a A)^3+27*(a B)^2))) :
    finitePair (S:=S) A B ≫ FiniteAdditionGluing318.addition A B hD=
      FiniteAdditionGluing318.addition (a A) (a B) hS ≫ coefficientMap A B := by
  apply (cancel_epi (pullbackSpecIso S (ShortAffineJacobian318.Ring (a A) (a B)) (ShortAffineJacobian318.Ring (a A) (a B))).inv).mp
  rw [←Category.assoc,tensor_pair,Category.assoc,FiniteAdditionGluing318.addition,
    Iso.inv_hom_id_assoc,←Category.assoc,FiniteAdditionGluing318.addition,Iso.inv_hom_id_assoc]
  exact FiniteCoefficientNaturality318.coordinate A B hD hS
end CompletedCoefficientProduct318
