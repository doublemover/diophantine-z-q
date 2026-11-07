module
public import InfinityAdditionAlgebra318
public import WeierstrassGluing318
public import RelativeChordScheme318
public section
noncomputable section
namespace InfinityAdditionScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ShortAffineJacobian318 InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def domain (A B:R) (tangent:Bool) : Scheme :=
  Spec (CommRingCat.of (OutputRing A B tangent))

/-- The actual infinity-output open in the same genuine finite-pair product. -/
@[expose] def intoProduct (A B:R) (tangent:Bool) :
    domain A B tangent ⟶ RelativeChordScheme318.productScheme A B :=
  Spec.map (CommRingCat.ofHom (pairMap A B tangent).toRingHom) ≫
    (pullbackSpecIso R (Ring A B) (Ring A B)).inv

instance intoProduct_open (A B:R) (tangent:Bool) : IsOpenImmersion (intoProduct A B tangent) := by
  have he : CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B tangent)
      (pairMap A B tangent).toRingHom =
      CommRingCat.ofHom (R:=PairRing A B) (S:=OutputRing A B tangent)
        (algebraMap (PairRing A B) (OutputRing A B tangent)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  have hh : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=PairRing A B)
      (S:=OutputRing A B tangent) (pairMap A B tangent).toRingHom)) := by
    rw [he]
    exact IsOpenImmersion.of_isLocalization (R:=PairRing A B)
      (S:=OutputRing A B tangent) (numeratorY A B tangent)
  dsimp only [intoProduct,domain,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

/-- Actual Scheme morphism into the whole Y=1 output chart. -/
@[expose] def chartAddition (A B:R) (tangent:Bool) : domain A B tangent ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (outputMap A B tangent).toRingHom)

/-- Its actual output in the completed two-chart curve. -/
@[expose] def addition (A B:R) (tangent:Bool) : domain A B tangent ⟶ WeierstrassGluing318.scheme A B :=
  chartAddition A B tangent ≫ WeierstrassGluing318.infinityChart A B

/-- The genuine infinity-output Scheme map preserves the original base. -/
theorem chart_over_base (A B:R) (tangent:Bool) :
    chartAddition A B tangent ≫ InfinitySmooth318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B tangent))) := by
  dsimp only [chartAddition,domain,InfinitySmooth318.scheme,InfinitySmooth318.structureMap]
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (outputMap A B tangent).commutes r

theorem addition_over_base (A B:R) (tangent:Bool) :
    addition A B tangent ≫ WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (OutputRing A B tangent))) := by
  rw [addition,Category.assoc,WeierstrassGluing318.infinityChart_structure,chart_over_base]

/-- Both actual input points are read from the same product coordinate algebra. -/
@[expose] def leftInput (A B:R) (tangent:Bool) : Ring A B →ₐ[R] OutputRing A B tangent :=
  (pairMap A B tangent).comp (leftPair A B)
@[expose] def rightInput (A B:R) (tangent:Bool) : Ring A B →ₐ[R] OutputRing A B tangent :=
  (pairMap A B tangent).comp (rightPair A B)

theorem intoProduct_fst (A B:R) (tangent:Bool) : intoProduct A B tangent ≫ pullback.fst _ _=
    Spec.map (CommRingCat.ofHom (leftInput A B tangent).toRingHom) := by
  dsimp only [intoProduct,domain,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [Category.assoc,pullbackSpecIso_inv_fst,←Spec.map_comp]
  rfl
theorem intoProduct_snd (A B:R) (tangent:Bool) : intoProduct A B tangent ≫ pullback.snd _ _=
    Spec.map (CommRingCat.ofHom (rightInput A B tangent).toRingHom) := by
  dsimp only [intoProduct,domain,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [Category.assoc,pullbackSpecIso_inv_snd,←Spec.map_comp]
  rfl

@[expose] def literalAddition (N:ℕ) (tangent:Bool) :=
  addition (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) tangent

end InfinityAdditionScheme318
