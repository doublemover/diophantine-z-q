module
public import FiniteLocalZero318
public import FiniteAdditionGluing318
public import AffineProductEvaluation318
public import SchemeAffineTestExt318
public section
noncomputable section
namespace FiniteZeroScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteAdditionLocal318 FinitePairSchemeCover318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def first (A B:R) : Spec (CommRingCat.of (RelativeChordAlgebra318.PairRing A B)) ⟶
    ShortAffineScheme318.scheme A B := Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.leftPair A B).toRingHom)
@[expose] def second (A B:R) : Spec (CommRingCat.of (RelativeChordAlgebra318.PairRing A B)) ⟶
    ShortAffineScheme318.scheme A B := Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.rightPair A B).toRingHom)
@[expose] def negation (A B:R) : ShortAffineScheme318.scheme A B ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom)
@[expose] def chartInto (A B:R) (i:Fin 4) : Spec (CommRingCat.of (LocalRing A B i)) ⟶
    Spec (CommRingCat.of (RelativeChordAlgebra318.PairRing A B)) :=
  Spec.map (CommRingCat.ofHom (inputMap A B i).toRingHom)

lemma local_algebra {S:Type u} [CommRing S] [Algebra R S]
    (A B:R) (i:Fin 4) (φ:LocalRing A B i →ₐ[R] S)
    (h:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ localAddition A B i=
      Spec.algebraMap R S ≫ WeierstrassGluing318.infinity A B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ chartInto A B i ≫ second A B=
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ chartInto A B i ≫ first A B ≫ negation A B := by
  have hh:=FiniteLocalZero318.input_maps A B i φ h
  dsimp only [chartInto,first,second,negation]
  simp only [←Spec.map_comp]
  exact congrArg (fun k:ShortAffineJacobian318.Ring A B →ₐ[R] S=>
    Spec.map (CommRingCat.ofHom k.toRingHom)) hh

lemma local_affine {S:Type u} [CommRing S] (A B:R) (i:Fin 4)
    (x:Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (LocalRing A B i)))
    (h:x ≫ localAddition A B i=x ≫ Spec.algebraMap R (LocalRing A B i) ≫ WeierstrassGluing318.infinity A B) :
    x ≫ chartInto A B i ≫ second A B=x ≫ chartInto A B i ≫ first A B ≫ negation A B := by
  obtain ⟨b,hb⟩:=Spec.map_surjective (x ≫ Spec.algebraMap R (LocalRing A B i))
  letI : Algebra R S:=b.hom.toAlgebra
  have hx:x ≫ Spec.algebraMap R (LocalRing A B i)=Spec.algebraMap R S:=hb.symm
  let φ:=AffineProductEvaluation318.toAlgHom x hx
  have hφ:Spec.map (CommRingCat.ofHom φ.toRingHom)=x:=AffineProductEvaluation318.map_toAlgHom x hx
  rw [←hφ]
  apply local_algebra
  rw [hφ,h,←Category.assoc,hx]

/-- The local zero-sum converse on arbitrary Scheme tests, not only affine or
field-valued tests. The coefficient algebra is induced by the actual base map. -/
theorem local_scheme {X:Scheme.{u}} (A B:R) (i:Fin 4)
    (x:X ⟶ Spec (CommRingCat.of (LocalRing A B i)))
    (h:x ≫ localAddition A B i=x ≫ Spec.algebraMap R (LocalRing A B i) ≫ WeierstrassGluing318.infinity A B) :
    x ≫ chartInto A B i ≫ second A B=x ≫ chartInto A B i ≫ first A B ≫ negation A B := by
  apply SchemeAffineTestExt318.hom_ext
  intro S t
  simpa only [Category.assoc] using local_affine A B i (t ≫ x)
    (by simpa only [Category.assoc] using congrArg (fun k=>t ≫ k) h)

@[reassoc] lemma chart_base (A B:R) (i:Fin 4) :
    chartInto A B i ≫ Spec.algebraMap R (RelativeChordAlgebra318.PairRing A B)=
      Spec.algebraMap R (LocalRing A B i) := by
  dsimp only [chartInto,Spec.algebraMap]
  rw [←Spec.map_comp]
  congr 1

/-- Exact global converse for the whole glued finite-input law. It follows
from its actual four-open cover and is valid over nonreduced bases. -/
theorem coordinate_zero {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (x:X ⟶ Spec (CommRingCat.of (RelativeChordAlgebra318.PairRing A B)))
    (h:x ≫ FiniteAdditionGluing318.coordinateAddition A B hD=
      x ≫ Spec.algebraMap R (RelativeChordAlgebra318.PairRing A B) ≫ WeierstrassGluing318.infinity A B) :
    x ≫ second A B=x ≫ first A B ≫ negation A B := by
  let U:=coordinateCover A B hD
  let V : X.OpenCover:=U.pullback₁ x
  apply V.hom_ext
  intro i
  have hp:U.pullbackHom x i ≫ chartInto A B i=(U.pullback₁ x).f i ≫ x:=U.pullbackHom_map x i
  have hr:chartInto A B i ≫ FiniteAdditionGluing318.coordinateAddition A B hD=localAddition A B i:=
    FiniteAdditionGluing318.coordinate_restriction A B hD i
  have hl:U.pullbackHom x i ≫ localAddition A B i=
      U.pullbackHom x i ≫ Spec.algebraMap R (LocalRing A B i) ≫ WeierstrassGluing318.infinity A B := by
    rw [←hr,←Category.assoc,hp,Category.assoc,h]
    rw [←Category.assoc ((U.pullback₁ x).f i) x,←hp,Category.assoc,chart_base_assoc]
  have hh:=local_scheme A B i (U.pullbackHom x i) hl
  simpa only [←Category.assoc,hp] using hh
end FiniteZeroScheme318
