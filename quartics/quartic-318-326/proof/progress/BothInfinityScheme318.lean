module
public import BothInfinityAlgebra318
public import WeierstrassGluing318
public section
noncomputable section
namespace BothInfinityScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits BothInfinityAlgebra318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def productScheme (A B:R) : Scheme :=
  pullback (InfinitySmooth318.structureMap A B) (InfinitySmooth318.structureMap A B)
@[expose] def domain (A B:R) : Scheme := Spec (CommRingCat.of (OutputRing A B))
@[expose] def intoProduct (A B:R) : domain A B ⟶ productScheme A B :=
  Spec.map (CommRingCat.ofHom (algebraMap (PairRing A B) (OutputRing A B))) ≫
    (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).inv

instance intoProduct_open (A B:R) : IsOpenImmersion (intoProduct A B) := by
  letI := IsOpenImmersion.of_isLocalization (S:=OutputRing A B) (domainElement A B)
  dsimp only [intoProduct,domain,productScheme,InfinitySmooth318.structureMap,InfinitySmooth318.scheme]
  infer_instance

@[expose] def chartAddition (A B:R) : domain A B ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (outputMap A B).toRingHom)
@[expose] def addition (A B:R) : domain A B ⟶ WeierstrassGluing318.scheme A B :=
  chartAddition A B ≫ WeierstrassGluing318.infinityChart A B

theorem chart_over_base (A B:R) : chartAddition A B ≫ InfinitySmooth318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B))) := by
  dsimp only [chartAddition,domain,InfinitySmooth318.scheme,InfinitySmooth318.structureMap]
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (outputMap A B).comp_algebraMap

theorem addition_over_base (A B:R) : addition A B ≫ WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B))) := by
  rw [addition,Category.assoc,WeierstrassGluing318.infinityChart_structure,chart_over_base]

@[expose] def leftInput (A B:R) : InfinityChart318.Ring A B →ₐ[R] OutputRing A B :=
  (pairMap A B).comp (leftPair A B)
@[expose] def rightInput (A B:R) : InfinityChart318.Ring A B →ₐ[R] OutputRing A B :=
  (pairMap A B).comp (rightPair A B)

theorem intoProduct_fst (A B:R) : intoProduct A B ≫ pullback.fst _ _=
    Spec.map (CommRingCat.ofHom (leftInput A B).toRingHom) := by
  dsimp only [intoProduct,domain,productScheme,InfinitySmooth318.structureMap,InfinitySmooth318.scheme]
  rw [Category.assoc,pullbackSpecIso_inv_fst,←Spec.map_comp]
  rfl
theorem intoProduct_snd (A B:R) : intoProduct A B ≫ pullback.snd _ _=
    Spec.map (CommRingCat.ofHom (rightInput A B).toRingHom) := by
  dsimp only [intoProduct,domain,productScheme,InfinitySmooth318.structureMap,InfinitySmooth318.scheme]
  rw [Category.assoc,pullbackSpecIso_inv_snd,←Spec.map_comp]
  rfl

@[expose] def literalAddition (N:ℕ) := addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end BothInfinityScheme318
