module
public import TangentOpenScheme318
public import RelativeChordScheme318
public section
noncomputable section
namespace TangentChordOverlap318
open ShortAffineJacobian318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- The genuine principal-open intersection algebra D((x2-x1)(y1+y2)). -/
@[expose] def bothDenominators (A B:R) : PairRing A B :=
  RelativeChordAlgebra318.gap A B*TangentOpenAlgebra318.ordinateSum A B
abbrev OverlapRing (A B:R) : Type u := Localization.Away (bothDenominators A B)

@[expose] def pairMap (A B:R) : PairRing A B →ₐ[R] OverlapRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (OverlapRing A B)

theorem two_units (A B:R) :
    IsUnit (pairMap A B (RelativeChordAlgebra318.gap A B)) ∧
    IsUnit (pairMap A B (TangentOpenAlgebra318.ordinateSum A B)) := by
  have hh:=IsLocalization.Away.algebraMap_isUnit (S:=OverlapRing A B) (bothDenominators A B)
  have hh' : IsUnit (pairMap A B (bothDenominators A B)) := hh
  simpa only [bothDenominators,map_mul,IsUnit.mul_iff] using hh'

@[expose] def fromChord (A B:R) : RelativeChordAlgebra318.ChordRing A B →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=IsScalarTower.toAlgHom R (PairRing A B) (OverlapRing (R:=R) A B))
    (RelativeChordAlgebra318.gap A B) (two_units A B).1
@[expose] def fromTangent (A B:R) : TangentOpenAlgebra318.TangentRing A B →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=IsScalarTower.toAlgHom R (PairRing A B) (OverlapRing (R:=R) A B))
    (TangentOpenAlgebra318.ordinateSum A B) (two_units A B).2

@[expose] def chordPairMap (A B:R) : PairRing A B →ₐ[R] RelativeChordAlgebra318.ChordRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (RelativeChordAlgebra318.ChordRing A B)
@[expose] def tangentPairMap (A B:R) : PairRing A B →ₐ[R] TangentOpenAlgebra318.TangentRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (TangentOpenAlgebra318.TangentRing A B)

@[simp] theorem fromChord_map (A B:R) (a:PairRing A B) :
    fromChord A B (chordPairMap A B a)=
      pairMap A B a := by
  simp [fromChord,pairMap,chordPairMap,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem fromTangent_map (A B:R) (a:PairRing A B) :
    fromTangent A B (tangentPairMap A B a)=
      pairMap A B a := by
  simp [fromTangent,pairMap,tangentPairMap,IsLocalization.Away.liftAlgHom_apply]

theorem left_coordinates (A B:R) (a:Ring A B) :
    fromChord A B (RelativeChordAlgebra318.left A B a)=
      fromTangent A B (TangentOpenAlgebra318.left A B a) := by
  change fromChord A B (chordPairMap A B (RelativeChordAlgebra318.leftPair A B a))=
    fromTangent A B (tangentPairMap A B (RelativeChordAlgebra318.leftPair A B a))
  rw [fromChord_map,fromTangent_map]
theorem right_coordinates (A B:R) (a:Ring A B) :
    fromChord A B (RelativeChordAlgebra318.right A B a)=
      fromTangent A B (TangentOpenAlgebra318.right A B a) := by
  change fromChord A B (chordPairMap A B (RelativeChordAlgebra318.rightPair A B a))=
    fromTangent A B (tangentPairMap A B (RelativeChordAlgebra318.rightPair A B a))
  rw [fromChord_map,fromTangent_map]

theorem slopes_agree (A B:R) :
    fromChord A B (RelativeChordAlgebra318.slope A B)=
      fromTangent A B (TangentOpenAlgebra318.slope A B) := by
  have h1:=congrArg (fromChord A B) (RelativeChordAlgebra318.slope_identity A B)
  have h2:=congrArg (fromTangent A B) (TangentOpenAlgebra318.slope_gap A B)
  simp only [map_mul,map_sub,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
    RelativeChordAlgebra318.y1,RelativeChordAlgebra318.y2,left_coordinates,right_coordinates] at h1
  simp only [map_mul,map_sub,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,
    TangentOpenAlgebra318.y1,TangentOpenAlgebra318.y2] at h2
  have hu: IsUnit (fromTangent A B (TangentOpenAlgebra318.x2 A B)-
      fromTangent A B (TangentOpenAlgebra318.x1 A B)) := by
    have hh:=(RelativeChordAlgebra318.gap_unit A B).map (fromChord A B)
    simpa only [map_sub,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
      TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,left_coordinates,right_coordinates] using hh
  exact hu.mul_right_cancel (h1.trans h2.symm)

/-- Exact equality of actual algebra maps on the genuine principal-open intersection. -/
theorem output_maps_agree (A B:R) :
    (fromChord A B).comp (RelativeChordAlgebra318.chordMap A B)=
      (fromTangent A B).comp (TangentOpenAlgebra318.tangentMap A B) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_x,
      TangentOpenAlgebra318.tangentMap_x,RelativeChordAlgebra318.x3,TangentOpenAlgebra318.x3,
      map_sub,map_pow,slopes_agree,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
      TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,left_coordinates,right_coordinates]
  · simp only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_y,
      TangentOpenAlgebra318.tangentMap_y,RelativeChordAlgebra318.y3,TangentOpenAlgebra318.y3,
      RelativeChordAlgebra318.x3,TangentOpenAlgebra318.x3,map_sub,map_mul,map_pow,slopes_agree,
      RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,RelativeChordAlgebra318.y1,
      TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,TangentOpenAlgebra318.y1,
      left_coordinates,right_coordinates]

open CategoryTheory AlgebraicGeometry in
/-- Therefore the two actual Scheme morphisms agree on this actual overlap. -/
theorem scheme_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (fromChord A B).toRingHom) ≫ RelativeChordScheme318.addition A B =
      Spec.map (CommRingCat.ofHom (fromTangent A B).toRingHom) ≫ TangentOpenScheme318.addition A B := by
  dsimp only [RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,
    TangentOpenScheme318.addition,TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (output_maps_agree A B))

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The actual D(gap*sum) open immersion in the same genuine affine fiber product. -/
@[expose] def overlapIntoProduct (A B:R) :
    Spec (CommRingCat.of (OverlapRing A B)) ⟶ RelativeChordScheme318.productScheme A B :=
  Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom) ≫
    (pullbackSpecIso R (Ring A B) (Ring A B)).inv

instance overlapIntoProduct_open (A B:R) : IsOpenImmersion (overlapIntoProduct A B) := by
  have he : CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom =
      CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (algebraMap (PairRing A B) (OverlapRing A B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  have hh : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom)) := by
    rw [he]
    exact IsOpenImmersion.of_isLocalization (R:=PairRing A B) (S:=OverlapRing A B) (bothDenominators A B)
  dsimp only [overlapIntoProduct,RelativeChordScheme318.productScheme,
    ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

/-- The actual overlap map factors through the ordinary-chord open. -/
theorem overlap_chord (A B:R) :
    Spec.map (CommRingCat.ofHom (fromChord A B).toRingHom) ≫
      RelativeChordScheme318.intoProduct A B=overlapIntoProduct A B := by
  dsimp only [RelativeChordScheme318.intoProduct,RelativeChordScheme318.chordOpen,
    RelativeChordScheme318.productScheme,ShortAffineScheme318.scheme,
    ShortAffineScheme318.structureMap,overlapIntoProduct]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fun a => fromChord_map A B a))

/-- The same actual overlap factors through the complementary tangent/secant open. -/
theorem overlap_tangent (A B:R) :
    Spec.map (CommRingCat.ofHom (fromTangent A B).toRingHom) ≫
      TangentOpenScheme318.intoProduct A B=overlapIntoProduct A B := by
  dsimp only [TangentOpenScheme318.intoProduct,TangentOpenScheme318.tangentOpen,
    TangentOpenScheme318.productScheme,RelativeChordScheme318.productScheme,ShortAffineScheme318.scheme,
    ShortAffineScheme318.structureMap,overlapIntoProduct]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fun a => fromTangent_map A B a))

end TangentChordOverlap318
