module
public import MixedFiniteInput318
public import InfinityInputCover318
public import FiniteAdditionGluing318
public section
noncomputable section
namespace MixedInputLocal318
open InfinityInputAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R]

abbrev FiniteRing (A B:R) := Localization.Away (v A B)
@[expose] def finiteInput (A B:R) : PairRing A B →ₐ[R] FiniteRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (FiniteRing A B)
lemma v_unit (A B:R) : IsUnit (finiteInput A B (v A B)) :=
  IsLocalization.Away.algebraMap_isUnit (S:=FiniteRing A B) (v A B)
@[expose] def finitePair (A B:R) : RelativeChordAlgebra318.PairRing A B →ₐ[R] FiniteRing A B :=
  MixedFiniteInput318.finitePair A B (finiteInput A B) (v_unit A B)
@[expose] def finiteAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec (CommRingCat.of (FiniteRing A B)) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (finitePair A B).toRingHom) ≫
    FiniteAdditionGluing318.coordinateAddition A B hD

@[expose] def fromFinite (A B:R) : FiniteRing A B →ₐ[R] InfinityInputOverlap318.OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=InfinityInputOverlap318.commonMap A B) (v A B)
    (InfinityInputOverlap318.two_units A B).2
@[simp] theorem fromFinite_pair (A B:R) (a:PairRing A B) :
    fromFinite A B (finiteInput A B a)=InfinityInputOverlap318.commonMap A B a := by
  simp [fromFinite,finiteInput,IsLocalization.Away.liftAlgHom_apply]

theorem overlap_finitePair (A B:R) :
    (fromFinite A B).comp (finitePair A B)=InfinityInputOverlap318.finitePair A B := by
  have he : (fromFinite A B).comp (finiteInput A B)=InfinityInputOverlap318.commonMap A B := by
    apply AlgHom.ext
    intro a
    exact fromFinite_pair A B a
  unfold finitePair
  rw [MixedFiniteInput318.finitePair_natural]
  simp only [he]
  rfl

theorem overlap_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Spec.map (CommRingCat.ofHom (fromFinite A B).toRingHom) ≫ finiteAddition A B hD=
      Spec.map (CommRingCat.ofHom (InfinityInputOverlap318.fromInput A B).toRingHom) ≫
        InfinityInputScheme318.addition A B := by
  rw [InfinityInputOverlapScheme318.output_agreement,finiteAddition,←Category.assoc,←Spec.map_comp]
  have hp : CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=FiniteRing A B) (finitePair A B).toRingHom ≫
      CommRingCat.ofHom (R:=FiniteRing A B) (S:=InfinityInputOverlap318.OverlapRing A B) (fromFinite A B).toRingHom=
      CommRingCat.ofHom (InfinityInputOverlap318.finitePair A B).toRingHom :=
    by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (overlap_finitePair A B)
  rw [hp]
  have hc : CommRingCat.ofHom (algebraMap (RelativeChordAlgebra318.PairRing A B)
      (RelativeChordAlgebra318.ChordRing A B)) ≫
      CommRingCat.ofHom (InfinityInputOverlap318.fromChord A B).toRingHom=
      CommRingCat.ofHom (InfinityInputOverlap318.finitePair A B).toRingHom := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (InfinityInputOverlap318.fromChord_pair A B)
  rw [←hc,Spec.map_comp,Category.assoc]
  change _ ≫ ((FinitePairSchemeCover318.coordinateCover A B hD).f (0:Fin 4) ≫
    FiniteAdditionGluing318.coordinateAddition A B hD)=_
  rw [FiniteAdditionGluing318.coordinate_restriction]
  rfl

section Generic
variable {S:Type u} [CommRing S] [Algebra R S]
/-- Compatibility on every coefficient algebra, including nonreduced algebras. -/
theorem generic_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:FiniteRing A B →ₐ[R] S) (ψ:OutputRing A B →ₐ[R] S)
    (hp:∀a:PairRing A B,φ (finiteInput A B a)=ψ (pairMap A B a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ finiteAddition A B hD=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ InfinityInputScheme318.addition A B := by
  let f:=φ.comp (finiteInput A B)
  have hv:IsUnit (f (v A B)):=(v_unit A B).map φ
  have hh:IsUnit (f (denominator A B)) := by
    change IsUnit (φ (finiteInput A B (denominator A B)))
    rw [hp]
    exact (denominator_unit A B).map ψ
  let χ:InfinityInputOverlap318.OverlapRing A B →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom (f:=f) (InfinityInputOverlap318.overlapDenominator A B)
      (by simpa only [InfinityInputOverlap318.overlapDenominator,map_mul] using hh.mul hv)
  have hχ (a:PairRing A B) : χ (InfinityInputOverlap318.commonMap A B a)=f a := by
    simp [χ,InfinityInputOverlap318.commonMap,IsLocalization.Away.liftAlgHom_apply]
  have hφ : χ.comp (fromFinite A B)=φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (v A B))
    apply AlgHom.ext
    intro a
    change χ (fromFinite A B (finiteInput A B a))=φ (finiteInput A B a)
    rw [fromFinite_pair,hχ]
    rfl
  have hψ : χ.comp (InfinityInputOverlap318.fromInput A B)=ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (denominator A B))
    apply AlgHom.ext
    intro a
    change χ (InfinityInputOverlap318.fromInput A B (pairMap A B a))=ψ (pairMap A B a)
    rw [InfinityInputOverlap318.fromInput_pair,hχ]
    exact hp a
  have he:=congrArg (fun k=>Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ k) (overlap_agreement A B hD)
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp] at he
  change Spec.map (CommRingCat.ofHom (χ.comp (fromFinite A B)).toRingHom) ≫ _=
    Spec.map (CommRingCat.ofHom (χ.comp (InfinityInputOverlap318.fromInput A B)).toRingHom) ≫ _ at he
  rwa [hφ,hψ] at he
end Generic
end MixedInputLocal318
