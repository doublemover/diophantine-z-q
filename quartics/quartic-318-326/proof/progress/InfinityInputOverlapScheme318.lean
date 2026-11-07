module
public import InfinityInputOverlap318
public import InfinityFiniteCompatibility318
public section
noncomputable section
namespace InfinityInputOverlapScheme318
open InfinityInputAlgebra318 InfinityInputOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[simp] theorem fromChord_x1 (A B:R) : fromChord A B (RelativeChordAlgebra318.x1 A B)=
    firstFinite A B (ShortAffineJacobian318.x A B) := by
  change fromChord A B (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.x A B)))=_
  rw [fromChord_pair,finitePair_left]
@[simp] theorem fromChord_y1 (A B:R) : fromChord A B (RelativeChordAlgebra318.y1 A B)=
    firstFinite A B (ShortAffineJacobian318.y A B) := by
  change fromChord A B (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.y A B)))=_
  rw [fromChord_pair,finitePair_left]
@[simp] theorem fromChord_x2 (A B:R) : fromChord A B (RelativeChordAlgebra318.x2 A B)=
    commonMap A B (x A B) := by
  change fromChord A B (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.x A B)))=_
  rw [fromChord_pair,finitePair_right]
  rfl
@[simp] theorem fromChord_y2 (A B:R) : fromChord A B (RelativeChordAlgebra318.y2 A B)=
    commonMap A B (y A B) := by
  change fromChord A B (TangentChordOverlap318.chordPairMap A B (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.y A B)))=_
  rw [fromChord_pair,finitePair_right]
  rfl

/-- The actual D(h*v) principal open in the genuine infinity-chart/finite-chart product. -/
@[expose] def intoProduct (A B:R) : Spec (CommRingCat.of (OverlapRing A B)) ⟶ InfinityInputScheme318.productScheme A B :=
  Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (commonMap A B).toRingHom) ≫
    (pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv
instance intoProduct_open (A B:R) : IsOpenImmersion (intoProduct A B) := by
  have he : CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (commonMap A B).toRingHom=
      CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (algebraMap (PairRing A B) (OverlapRing A B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  have hh : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (commonMap A B).toRingHom)) := by
    rw [he]
    exact IsOpenImmersion.of_isLocalization (R:=PairRing A B) (S:=OverlapRing A B) (overlapDenominator A B)
  dsimp only [intoProduct,InfinityInputScheme318.productScheme,InfinitySmooth318.scheme,InfinitySmooth318.structureMap,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

/-- This actual overlap factors through the constructed infinity-input addition domain. -/
theorem into_input (A B:R) : Spec.map (CommRingCat.ofHom (fromInput A B).toRingHom) ≫
    InfinityInputScheme318.intoProduct A B=intoProduct A B := by
  dsimp only [InfinityInputScheme318.intoProduct,InfinityInputScheme318.domain,intoProduct,
    InfinityInputScheme318.productScheme,InfinitySmooth318.scheme,InfinitySmooth318.structureMap,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fromInput_pair A B))

/-- Both actual output morphisms agree on the concrete overlap, with all input-transition
premises discharged from the original chart localization maps. -/
theorem output_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (fromInput A B).toRingHom) ≫ InfinityInputScheme318.addition A B=
      Spec.map (CommRingCat.ofHom (fromChord A B).toRingHom) ≫ RelativeChordScheme318.addition A B ≫
        WeierstrassGluing318.finiteChart A B := by
  apply InfinityInputFiniteOverlap318.scheme_agreement
  · rw [fromInput_pair,fromInput_pair,fromChord_x1]
    exact (first_x_relation A B).symm
  · rw [fromInput_pair,fromChord_y1]
    exact first_y_relation A B
  · rw [fromInput_pair,fromChord_x2]
  · rw [fromInput_pair,fromChord_y2]

/-- The first input maps are genuinely equal in the completed curve, using its actual
finite/infinity overlap rather than equality on field points. -/
theorem first_input_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (firstInfinity A B).toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.map (CommRingCat.ofHom (firstFinite A B).toRingHom) ≫ WeierstrassGluing318.finiteChart A B := by
  apply InfinityFiniteCompatibility318.scheme_agreement
  · change commonMap A B (u A B)*firstFinite A B (ShortAffineJacobian318.y A B)=_
    rw [←first_x_relation A B]
    calc
      _=firstFinite A B (ShortAffineJacobian318.x A B)*(firstFinite A B (ShortAffineJacobian318.y A B)*commonMap A B (v A B)) := by ring
      _=_ := by rw [first_y_relation,mul_one]
  · change commonMap A B (v A B)*firstFinite A B (ShortAffineJacobian318.y A B)=1
    rw [mul_comm,first_y_relation]

end InfinityInputOverlapScheme318
