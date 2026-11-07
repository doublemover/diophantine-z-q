module
public import InfinityInputOrigin318
public import WeierstrassGluing318
import all InfinitySmooth318
public section
noncomputable section
namespace InfinityInputScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityInputAlgebra318 InfinityInputOrigin318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def productScheme (A B:R) : Scheme :=
  pullback (InfinitySmooth318.structureMap A B) (ShortAffineScheme318.structureMap A B)
@[expose] def domain (A B:R) : Scheme := Spec (CommRingCat.of (OutputRing A B))
@[expose] def intoProduct (A B:R) : domain A B ⟶ productScheme A B :=
  Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B) (pairMap A B).toRingHom) ≫
    (pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv
instance intoProduct_open (A B:R) : IsOpenImmersion (intoProduct A B) := by
  have he : CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B) (pairMap A B).toRingHom=
      CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B) (algebraMap (PairRing A B) (OutputRing A B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  have hh : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B) (pairMap A B).toRingHom)) := by
    rw [he]
    exact IsOpenImmersion.of_isLocalization (R:=PairRing A B) (S:=OutputRing A B) (denominator A B)
  dsimp only [intoProduct,domain,productScheme,InfinitySmooth318.scheme,InfinitySmooth318.structureMap,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

@[expose] def finiteAddition (A B:R) : domain A B ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom (outputMap A B).toRingHom)
@[expose] def addition (A B:R) : domain A B ⟶ WeierstrassGluing318.scheme A B :=
  finiteAddition A B ≫ WeierstrassGluing318.finiteChart A B

theorem finiteAddition_over_base (A B:R) : finiteAddition A B ≫ ShortAffineScheme318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B))) := by
  dsimp only [finiteAddition,ShortAffineScheme318.structureMap,ShortAffineScheme318.scheme,domain]
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (outputMap A B).commutes r

theorem addition_over_base (A B:R) : addition A B ≫ WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B))) := by
  rw [addition,Category.assoc,WeierstrassGluing318.finiteChart_structure,finiteAddition_over_base]

/-- The entire actual infinity-times-finite locus factors through this open. -/
@[expose] def infinityInput (A B:R) : ShortAffineScheme318.scheme A B ⟶ domain A B :=
  Spec.map (CommRingCat.ofHom (originLift A B).toRingHom)

/-- Its first input is the actual infinity section, not just a point with zero coordinates. -/
theorem infinityInput_fst (A B:R) : infinityInput A B ≫ intoProduct A B ≫ pullback.fst _ _=
    ShortAffineScheme318.structureMap A B ≫ InfinitySmooth318.infinity A B := by
  dsimp only [infinityInput,intoProduct,domain,productScheme,InfinitySmooth318.scheme,InfinitySmooth318.structureMap,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap,InfinitySmooth318.infinity]
  rw [Category.assoc,pullbackSpecIso_inv_fst,←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (originLift_pair A B (left A B a)).trans (originPair_left A B a)

/-- Its second input is the identity morphism of the whole actual finite chart. -/
theorem infinityInput_snd (A B:R) : infinityInput A B ≫ intoProduct A B ≫ pullback.snd _ _=𝟙 _ := by
  dsimp only [infinityInput,intoProduct,domain,productScheme,InfinitySmooth318.scheme,InfinitySmooth318.structureMap,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [Category.assoc,pullbackSpecIso_inv_snd,←Spec.map_comp,←Spec.map_comp]
  change Spec.map _=𝟙 (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B)))
  rw [←Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (originLift_pair A B (right A B a)).trans (originPair_right A B a)

/-- The actual relative unit law along infinity times the entire finite chart. -/
theorem infinityInput_addition (A B:R) : infinityInput A B ≫ addition A B=WeierstrassGluing318.finiteChart A B := by
  dsimp only [infinityInput,addition,finiteAddition]
  rw [←Category.assoc,←Spec.map_comp]
  have he : CommRingCat.ofHom (outputMap A B).toRingHom ≫ CommRingCat.ofHom (originLift A B).toRingHom=
      𝟙 (CommRingCat.of (ShortAffineJacobian318.Ring A B)) := by
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (origin_output_identity A B))
  rw [he,Spec.map_id]
  change 𝟙 (ShortAffineScheme318.scheme A B) ≫ WeierstrassGluing318.finiteChart A B=_
  exact Category.id_comp _

@[expose] def literalAddition (N:ℕ) := addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end InfinityInputScheme318
