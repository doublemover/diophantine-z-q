module
public import MixedInputLocal318
public section
noncomputable section
namespace MixedAdditionGluing318
open InfinityInputAlgebra318 InfinityInputCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R]
abbrev LocalRing (A B:R) (i:Fin 2) := Localization.Away (chartElement A B i)
@[expose] def inputMap (A B:R) (i:Fin 2) : PairRing A B →ₐ[R] LocalRing A B i :=
  IsScalarTower.toAlgHom R (PairRing A B) (LocalRing A B i)
@[expose] def localAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 2) :
    Spec (CommRingCat.of (LocalRing A B i)) ⟶ WeierstrassGluing318.scheme A B := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · exact MixedInputLocal318.finiteAddition A B hD
  · exact InfinityInputScheme318.addition A B
abbrev CommonRing (A B:R) (i j:Fin 2) := LocalRing A B i ⊗[PairRing A B] LocalRing A B j
@[expose] def left (A B:R) (i j:Fin 2) : LocalRing A B i →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R
@[expose] def right (A B:R) (i j:Fin 2) : LocalRing A B j →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R
lemma same_pair (A B:R) (i j:Fin 2) (a:PairRing A B) :
    left A B i j (inputMap A B i a)=right A B i j (inputMap A B j a) := by
  exact ((Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).commutes a).trans
    ((Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).commutes a).symm

theorem local_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    Spec.map (CommRingCat.ofHom (left A B i j).toRingHom) ≫ localAddition A B hD i=
      Spec.map (CommRingCat.ofHom (right A B i j).toRingHom) ≫ localAddition A B hD j := by
  by_cases hij:i=j
  · subst j
    have he:left A B i i=right A B i i := by
      apply IsLocalization.algHom_ext (Submonoid.powers (chartElement A B i))
      apply AlgHom.ext
      exact same_pair A B i i
    rw [he]
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact MixedInputLocal318.generic_agreement A B hD (left A B 0 1) (right A B 0 1) (same_pair A B 0 1)
  · exact (MixedInputLocal318.generic_agreement A B hD (right A B 1 0) (left A B 1 0)
      (fun a=>(same_pair A B 1 0 a).symm)).symm

theorem coordinate_compatibility (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    pullback.fst ((coordinateCover A B).f i) ((coordinateCover A B).f j) ≫ localAddition A B hD i=
      pullback.snd _ _ ≫ localAddition A B hD j := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B i))))
      (Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (LocalRing A B j)))) ≫ localAddition A B hD i=
    pullback.snd _ _ ≫ localAddition A B hD j
  apply (cancel_epi (pullbackSpecIso (PairRing A B) (LocalRing A B i) (LocalRing A B j)).inv).mp
  rw [←Category.assoc,pullbackSpecIso_inv_fst,←Category.assoc,pullbackSpecIso_inv_snd]
  exact local_agreement A B hD i j

/-- Actual addition over the whole infinity-chart times finite-chart input product. -/
@[expose] def coordinateAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec (CommRingCat.of (PairRing A B)) ⟶ WeierstrassGluing318.scheme A B :=
  (coordinateCover A B).glueMorphisms (localAddition A B hD) (coordinate_compatibility A B hD)
theorem coordinate_restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 2) :
    (coordinateCover A B).f i ≫ coordinateAddition A B hD=localAddition A B hD i :=
  (coordinateCover A B).ι_glueMorphisms _ _ i
@[expose] def addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    InfinityInputScheme318.productScheme A B ⟶ WeierstrassGluing318.scheme A B :=
  (pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫
    coordinateAddition A B hD

theorem restriction (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 2) :
    (productCover A B).f i ≫ addition A B hD=localAddition A B hD i := by
  change ((coordinateCover A B).f i ≫
      (pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv) ≫
      ((pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).hom ≫
      coordinateAddition A B hD)=_
  rw [Category.assoc,Iso.inv_hom_id_assoc,coordinate_restriction]

lemma local_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 2) :
    localAddition A B hD i ≫ WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (LocalRing A B i))) := by
  fin_cases i
  · change (Spec.map (CommRingCat.ofHom (MixedInputLocal318.finitePair A B).toRingHom) ≫
        FiniteAdditionGluing318.coordinateAddition A B hD) ≫ _=_
    rw [Category.assoc,FiniteAdditionGluing318.coordinate_over_base,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (MixedInputLocal318.finitePair A B).comp_algebraMap
  · exact InfinityInputScheme318.addition_over_base A B

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
      pullback.fst (InfinitySmooth318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        InfinitySmooth318.structureMap A B := by
  rw [addition,Category.assoc,coordinate_over_base]
  dsimp only [InfinitySmooth318.structureMap,InfinitySmooth318.scheme,
    ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme]
  apply (cancel_epi (pullbackSpecIso R (InfinityChart318.Ring A B)
    (ShortAffineJacobian318.Ring A B)).inv).mp
  rw [Iso.inv_hom_id_assoc,←Category.assoc,pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (algebraMap R (PairRing A B)))=
    Spec.map (CommRingCat.ofHom (InfinityInputAlgebra318.left A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityChart318.Ring A B)))
  rw [←Spec.map_comp]
  congr 1

/-- The glued mixed law has the actual relative infinity-section identity on the whole finite chart. -/
theorem infinityInput_addition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    InfinityInputScheme318.infinityInput A B ≫ InfinityInputScheme318.intoProduct A B ≫
      addition A B hD=WeierstrassGluing318.finiteChart A B := by
  rw [←InfinityInputCover318.productCover_infinityInput,restriction]
  exact InfinityInputScheme318.infinityInput_addition A B

@[expose] def literalAddition (N:ℕ) :=
  addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
end MixedAdditionGluing318
