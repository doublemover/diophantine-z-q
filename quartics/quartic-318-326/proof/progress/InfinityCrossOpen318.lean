module
public import InfinityCrossMaps318
public section
noncomputable section
namespace InfinityCrossOpen318
open InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def bothNumerators (A B:R) : PairRing A B := numeratorY A B false*numeratorY A B true
abbrev OverlapRing (A B:R) := Localization.Away (bothNumerators A B)
@[expose] def pairMap (A B:R) : PairRing A B →ₐ[R] OverlapRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (OverlapRing A B)

theorem two_units (A B:R) : IsUnit (pairMap A B (numeratorY A B false)) ∧
    IsUnit (pairMap A B (numeratorY A B true)) := by
  have hh : IsUnit (pairMap A B (bothNumerators A B)):=
    IsLocalization.Away.algebraMap_isUnit (S:=OverlapRing A B) (bothNumerators A B)
  simpa only [bothNumerators,map_mul,IsUnit.mul_iff] using hh

@[expose] def fromChord (A B:R) : OutputRing A B false →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=pairMap A B) (numeratorY A B false) (two_units A B).1
@[expose] def fromTangent (A B:R) : OutputRing A B true →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=pairMap A B) (numeratorY A B true) (two_units A B).2

@[simp] theorem fromChord_map (A B:R) (a:PairRing A B) :
    fromChord A B (InfinityAdditionAlgebra318.pairMap A B false a)=pairMap A B a := by
  simp [fromChord,InfinityAdditionAlgebra318.pairMap,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem fromTangent_map (A B:R) (a:PairRing A B) :
    fromTangent A B (InfinityAdditionAlgebra318.pairMap A B true a)=pairMap A B a := by
  simp [fromTangent,InfinityAdditionAlgebra318.pairMap,IsLocalization.Away.liftAlgHom_apply]

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Actual principal-open intersection in the genuine finite-pair fiber product. -/
@[expose] def intoProduct (A B:R) : Spec (CommRingCat.of (OverlapRing A B)) ⟶ RelativeChordScheme318.productScheme A B :=
  Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom) ≫
    (pullbackSpecIso R (ShortAffineJacobian318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv
instance intoProduct_open (A B:R) : IsOpenImmersion (intoProduct A B) := by
  have he : CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom=
      CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (algebraMap (PairRing A B) (OverlapRing A B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  have hh : IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=PairRing A B) (S:=OverlapRing A B) (pairMap A B).toRingHom)) := by
    rw [he]
    exact IsOpenImmersion.of_isLocalization (R:=PairRing A B) (S:=OverlapRing A B) (bothNumerators A B)
  dsimp only [intoProduct,RelativeChordScheme318.productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  infer_instance

theorem into_chord (A B:R) : Spec.map (CommRingCat.ofHom (fromChord A B).toRingHom) ≫
    InfinityAdditionScheme318.intoProduct A B false=intoProduct A B := by
  dsimp only [InfinityAdditionScheme318.intoProduct,InfinityAdditionScheme318.domain,intoProduct,
    RelativeChordScheme318.productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fromChord_map A B))
theorem into_tangent (A B:R) : Spec.map (CommRingCat.ofHom (fromTangent A B).toRingHom) ≫
    InfinityAdditionScheme318.intoProduct A B true=intoProduct A B := by
  dsimp only [InfinityAdditionScheme318.intoProduct,InfinityAdditionScheme318.domain,intoProduct,
    RelativeChordScheme318.productScheme,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fromTangent_map A B))

/-- Both actual infinity-output morphisms agree on their genuine principal-open intersection. -/
theorem scheme_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (fromChord A B).toRingHom) ≫ InfinityAdditionScheme318.addition A B false=
      Spec.map (CommRingCat.ofHom (fromTangent A B).toRingHom) ≫ InfinityAdditionScheme318.addition A B true := by
  apply InfinityCrossMaps318.scheme_agreement
  intro a
  rw [fromChord_map,fromTangent_map]

end InfinityCrossOpen318
