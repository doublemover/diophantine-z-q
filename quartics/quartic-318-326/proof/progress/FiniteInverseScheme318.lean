module
public import FiniteInverseLocal318
public section
noncomputable section
namespace FiniteInverseScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FiniteAntiDiagonal318 FiniteInverseLocal318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)
local instance pairCommRing : CommRing (RelativeChordAlgebra318.PairRing A B):=inferInstance
local instance pairAlgebra : Algebra R (RelativeChordAlgebra318.PairRing A B):=inferInstance

@[expose] def coordinateAnti : ShortAffineScheme318.scheme A B⟶
    Spec (CommRingCat.of (RelativeChordAlgebra318.PairRing A B)):=
  Spec.map (CommRingCat.ofHom (pair A B).toRingHom)

/-- The actual anti-diagonal in the genuine relative finite-input product. -/
@[expose] def antiDiagonal : ShortAffineScheme318.scheme A B⟶
    RelativeChordScheme318.productScheme A B:=
  coordinateAnti A B≫(pullbackSpecIso R (Curve A B) (Curve A B)).inv

lemma antiDiagonal_fst : antiDiagonal A B≫pullback.fst _ _=𝟙 _:=by
  dsimp only [antiDiagonal,coordinateAnti,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap,Curve,RelativeChordAlgebra318.PairRing]
  rw [Category.assoc,pullbackSpecIso_inv_fst]
  rw [←Spec.map_comp]
  have hh:(pair A B).comp (RelativeChordAlgebra318.leftPair A B)=AlgHom.id R (Curve A B):=
    AlgHom.ext (pair_left A B)
  exact (congrArg (fun f:Curve A B→ₐ[R]Curve A B=>Spec.map (CommRingCat.ofHom f.toRingHom)) hh).trans
    (Spec.map_id _)

lemma antiDiagonal_snd : antiDiagonal A B≫pullback.snd _ _=
    Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom):=by
  dsimp only [antiDiagonal,coordinateAnti,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap,Curve,RelativeChordAlgebra318.PairRing]
  rw [Category.assoc,pullbackSpecIso_inv_snd]
  rw [←Spec.map_comp]
  have hh:(pair A B).comp (RelativeChordAlgebra318.rightPair A B)=ChartNegation318.affineNeg A B:=
    AlgHom.ext (pair_right A B)
  exact congrArg (fun f:Curve A B→ₐ[R]Curve A B=>Spec.map (CommRingCat.ofHom f.toRingHom)) hh

lemma inverse_base_condition : (𝟙 (ShortAffineScheme318.scheme A B))≫ShortAffineScheme318.structureMap A B=
    Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom)≫
      ShortAffineScheme318.structureMap A B:=by
  have h:=congrArg (fun f=>antiDiagonal A B≫f)
    (pullback.condition (f:=ShortAffineScheme318.structureMap A B)
      (g:=ShortAffineScheme318.structureMap A B))
  simpa only [←Category.assoc,antiDiagonal_fst,antiDiagonal_snd] using h

/-- The constructed map is exactly the categorical anti-diagonal of identity
and the actual affine negation. -/
lemma antiDiagonal_eq_lift : antiDiagonal A B=
    pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom))
      (inverse_base_condition A B):=by
  apply pullback.hom_ext
  · rw [antiDiagonal_fst,pullback.lift_fst]
    rfl
  · rw [antiDiagonal_snd,pullback.lift_snd]

variable (hD:IsUnit (-16*(4*A^3+27*B^2)))
@[expose] def cover : (ShortAffineScheme318.scheme A B).OpenCover:=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (Curve A B))
    (denominator A B) (span_top A B hD)).openCover

lemma infinity_restriction (t:Bool) :
    Spec.map (CommRingCat.ofHom (InfinityAdditionAlgebra318.pairMap A B t).toRingHom)≫
      FiniteAdditionGluing318.coordinateAddition A B hD=InfinityAdditionScheme318.addition A B t:=by
  cases t
  · exact FiniteAdditionGluing318.coordinate_restriction A B hD 2
  · exact FiniteAdditionGluing318.coordinate_restriction A B hD 3

lemma local_anti (t:Bool) :
    (cover A B hD).f t≫coordinateAnti A B=
      Spec.map (CommRingCat.ofHom (toOutput A B t).toRingHom)≫
        Spec.map (CommRingCat.ofHom (InfinityAdditionAlgebra318.pairMap A B t).toRingHom):=by
  change Spec.map (CommRingCat.ofHom (algebraMap (Curve A B) (Local A B t)))≫
    Spec.map (CommRingCat.ofHom (pair A B).toRingHom)=_
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (toOutput_pair A B t z).symm

/-- Whole-curve inverse identity for the actual finite-input law, with no
reducedness or field hypothesis. -/
theorem coordinate_inverse :
    coordinateAnti A B≫FiniteAdditionGluing318.coordinateAddition A B hD=
      ShortAffineScheme318.structureMap A B≫WeierstrassGluing318.infinity A B:=by
  apply (cover A B hD).hom_ext
  intro t
  rw [←Category.assoc,local_anti,Category.assoc,infinity_restriction,scheme_inverse]
  rw [←Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (algebraMap R (Local A B t)))=
    Spec.map (CommRingCat.ofHom (algebraMap (Curve A B) (Local A B t)))≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Curve A B)))
  rw [←Spec.map_comp]
  congr 1

/-- Actual finite P plus actual finite −P is the actual infinity section. -/
theorem antiDiagonal_addition : antiDiagonal A B≫FiniteAdditionGluing318.addition A B hD=
    ShortAffineScheme318.structureMap A B≫WeierstrassGluing318.infinity A B:=by
  rw [antiDiagonal,FiniteAdditionGluing318.addition,Category.assoc,Iso.inv_hom_id_assoc]
  exact coordinate_inverse A B hD
end FiniteInverseScheme318
