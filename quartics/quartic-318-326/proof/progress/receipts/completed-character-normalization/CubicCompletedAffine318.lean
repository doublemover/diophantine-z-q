module
public import CompletedCharacterTargetFinite318
public import SourceCharacterGlobal318
public section
noncomputable section
namespace CubicCompletedAffine318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterBaseComparison318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing exact cubic/published affine isomorphism, followed by the
actual finite-chart inclusion of the completed Weierstrass target. -/
@[expose] def embedding (i:Fin 4):Spec (CommRingCat.of (SourceCharacterAlgebra318.Cubic i))⟶Target i:=
  (CubicPublishedScheme318.affineIso i).inv≫WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)
instance embedding_open (i:Fin 4):IsOpenImmersion (embedding i):=by
  unfold embedding
  infer_instance

lemma adjusted_x (i:Fin 4):
    algebraMap ℚ (SourceCharacterAlgebra318.Cubic i) (slope i:ℚ)*
      (CubicPublishedScheme318.coordinateEquiv i).symm (ShortAffineJacobian318.x (publishedA i) (publishedB i))+
        algebraMap ℚ (SourceCharacterAlgebra318.Cubic i) (centroid i)=
      algebraMap ℚ[X] (SourceCharacterAlgebra318.Cubic i) X:=by
  rw [CubicInverseCoordinates318.inverse_x,←mul_assoc,←map_mul]
  change algebraMap ℚ (SourceCharacterAlgebra318.Cubic i)
      ((↑(CubicInverseCoordinates318.xScale i)⁻¹:ℚ)*(CubicInverseCoordinates318.xScale i:ℚ))*_+_=_
  rw [Units.inv_mul,map_one,one_mul,sub_add_cancel]

variable (i:Fin 4) (L:P1⟶P1)
  (hL:JLineAtlas318.chart ℚ 1≫L=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1)

include hL in
/-- The entire actual cubic affine chart has the original t-structure map
under the exact completed-target coordinate transformation. -/
theorem factor:
    embedding i≫WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L=
      SourceCharacterGlobal318.coverMap i:=by
  rw [embedding]
  simp only [Category.assoc]
  rw [←Category.assoc (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
      (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)) L,
    WeierstrassXProjection318.finiteChart_xMap]
  rw [WeierstrassXProjection318.finiteProjection,Category.assoc,hL]
  change Spec.map (CommRingCat.ofHom (CubicPublishedScheme318.coordinateEquiv i).symm.toRingHom)≫
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (ShortAffineJacobian318.x (publishedA i) (publishedB i))).toRingHom)≫
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (SourceCharacterAlgebra318.Cubic i)))≫JLineAtlas318.chart ℚ 1
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change (CubicPublishedScheme318.coordinateEquiv i).symm
      ((Polynomial.aeval (R:=ℚ) (ShortAffineJacobian318.x (publishedA i) (publishedB i)))
        ((Polynomial.aeval (R:=ℚ) (affinePolynomial i)) (C r)))=
      algebraMap ℚ[X] (SourceCharacterAlgebra318.Cubic i) (C r)
    rw [Polynomial.aeval_C,show algebraMap ℚ ℚ[X] r=C r from rfl,
      Polynomial.aeval_C,AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (SourceCharacterAlgebra318.Cubic i) r
  · change (CubicPublishedScheme318.coordinateEquiv i).symm
      ((Polynomial.aeval (R:=ℚ) (ShortAffineJacobian318.x (publishedA i) (publishedB i)))
        ((Polynomial.aeval (R:=ℚ) (affinePolynomial i)) X))=
      algebraMap ℚ[X] (SourceCharacterAlgebra318.Cubic i) X
    simp only [Polynomial.aeval_X,affinePolynomial,map_add,map_mul,Polynomial.aeval_C,AlgEquiv.commutes]
    exact adjusted_x i
end CubicCompletedAffine318
