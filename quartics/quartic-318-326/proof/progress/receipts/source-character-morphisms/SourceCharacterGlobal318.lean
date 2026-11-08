module
public import SourceCharacterAffine318
public section
noncomputable section
namespace SourceCharacterGlobal318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318 SourceCharacterAlgebra318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance cubicFinite (i:Fin 4):Module.Finite R (Cubic i):=FourRootOrder318.root_finite _

@[expose] def cubicBaseMap (i:Fin 4):Spec (CommRingCat.of (Cubic i))⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (Cubic i)))
instance cubicBaseMap_finite (i:Fin 4):IsFinite (cubicBaseMap i):=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr (cubicFinite i))
@[expose] def coverMap (i:Fin 4):Spec (CommRingCat.of (Cubic i))⟶ProjectiveJLine318.scheme ℚ:=
  cubicBaseMap i≫JLineAtlas318.chart ℚ 1
instance coverMap_quasiCompact (i:Fin 4):QuasiCompact (coverMap i):=by
  unfold coverMap
  infer_instance
instance coverMap_separated (i:Fin 4):IsSeparated (coverMap i):=by
  unfold coverMap
  infer_instance
instance coverMap_finiteType (i:Fin 4):LocallyOfFiniteType (coverMap i):=by
  unfold coverMap
  infer_instance
instance coverMap_quasiFinite (i:Fin 4):LocallyQuasiFinite (coverMap i):=by
  unfold coverMap
  infer_instance

abbrev Model (i:Fin 4):Scheme:=(coverMap i).normalization
@[expose] def modelMap (i:Fin 4):Model i⟶ProjectiveJLine318.scheme ℚ:=
  (coverMap i).fromNormalization
instance modelMap_integral (i:Fin 4):IsIntegralHom (modelMap i):=by
  unfold modelMap
  infer_instance

theorem cubicOpen_open (i:Fin 4):IsOpenImmersion (coverMap i).toNormalization:=inferInstance
theorem cubicOpen_dense (i:Fin 4):IsDominant (coverMap i).toNormalization:=inferInstance

theorem model_integral (i:Fin 4):IsIntegral (Model i):=by
  letI:IsDomain (Cubic i):=(CubicCharacterFraction318.embedding_injective i).isDomain
  letI:IsIntegral (Spec (CommRingCat.of (Cubic i))):=inferInstance
  infer_instance

@[expose] def originalToCubic (i:Fin 4):ContactKummerCover318.cover units⟶
    Spec (CommRingCat.of (Cubic i)):=
  Spec.map (CommRingCat.ofHom
    ((SourceOpenFractionField318.orderToOpen units).comp (toSource i).toRingHom))

theorem original_factor (i:Fin 4):
    originalToCubic i≫coverMap i=ContactProjectiveModel318.coverMap units:=by
  rw [ContactGlobalProper318.finite_factor,originalToCubic,coverMap,cubicBaseMap,
    ←Spec.map_comp_assoc]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change SourceOpenFractionField318.orderToOpen units
    (toSource i (algebraMap R (Cubic i) p))=ContactGlobalProper318.finitePolynomial units p
  rw [AlgHom.commutes,SourceOpenFractionField318.orderToOpen_on_polynomial]
  rfl

/-- An actual global morphism from the existing contact normalization to
its literal cubic character normalization over the same projective line. -/
@[expose] def globalMap (i:Fin 4):ContactProjectiveModel318.model units⟶Model i:=
  (ContactProjectiveModel318.coverMap units).normalizationDesc
    (originalToCubic i≫(coverMap i).toNormalization) (modelMap i)
    (by rw [Category.assoc,modelMap,(coverMap i).toNormalization_fromNormalization]
        exact (original_factor i).symm)

theorem globalMap_over_line (i:Fin 4):
    globalMap i≫modelMap i=ContactProjectiveModel318.modelMap units:=
  (ContactProjectiveModel318.coverMap units).normalizationDesc_comp _ _ _

theorem globalMap_on_original (i:Fin 4):
    ContactProjectiveModel318.sourceOpen units≫globalMap i=
      originalToCubic i≫(coverMap i).toNormalization:=
  (ContactProjectiveModel318.coverMap units).toNormalization_normalizationDesc _ _ _

/-- Finiteness uses the actual already proved finite contact map, not an
assumption about the new target normalization. -/
theorem globalMap_finite (i:Fin 4):IsFinite (globalMap i):=by
  letI:IsFinite (globalMap i≫modelMap i):=by
    rw [globalMap_over_line]
    exact ContactGlobalProper318.normalization_finite units
  exact IsFinite.of_comp (globalMap i) (modelMap i)

lemma orderToOpen_injective : Function.Injective (SourceOpenFractionField318.orderToOpen units):=by
  intro x y h
  apply ContactKummerOrder318.embedding_injective units
  rw [←SourceOpenFractionField318.openEmbedding_on_order,←SourceOpenFractionField318.openEmbedding_on_order]
  exact congrArg (SourceOpenFractionField318.openEmbedding units) h

theorem originalToCubic_dominant (i:Fin 4):IsDominant (originalToCubic i):=by
  constructor
  change DenseRange (PrimeSpectrum.comap
    ((SourceOpenFractionField318.orderToOpen units).comp (toSource i).toRingHom))
  have hi:Function.Injective
      ((SourceOpenFractionField318.orderToOpen units).comp (toSource i).toRingHom):=by
    intro x y h
    apply toSource_injective i
    apply orderToOpen_injective
    exact h
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp hi]
  exact bot_le

theorem globalMap_dominant (i:Fin 4):IsDominant (globalMap i):=by
  letI:=originalToCubic_dominant i
  letI:=cubicOpen_dense i
  letI:IsDominant (ContactProjectiveModel318.sourceOpen units≫globalMap i):=by
    rw [globalMap_on_original]
    infer_instance
  exact IsDominant.of_comp (ContactProjectiveModel318.sourceOpen units) (globalMap i)

/-- The actual finite global character morphism is surjective on every
point of its actual relative-normalization target. -/
theorem globalMap_surjective (i:Fin 4):Surjective (globalMap i):=by
  letI:=globalMap_finite i
  letI:=globalMap_dominant i
  infer_instance
end SourceCharacterGlobal318
