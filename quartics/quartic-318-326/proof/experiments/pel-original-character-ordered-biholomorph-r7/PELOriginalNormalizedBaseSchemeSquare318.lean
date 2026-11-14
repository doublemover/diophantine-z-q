module
public import PELOriginalOrderedBaseSchemeNormalization318
public import NormalizedLegendreSchemeProjection318
public section
noncomputable section
namespace PELOriginalNormalizedBaseSchemeSquare318
open AlgebraicGeometry CategoryTheory Polynomial
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterSchemeMaps318 PELOriginalWholeCharacterMorphisms318
open PELOriginalOrderedBaseSchemeNormalization318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma center_eq (i:Fin 4):center i=branch i 0+difference i*
    NormalizedLegendreProjectiveModel318.shift (PELOriginalOrderedCharacterCoordinate318.parameter i):=by
  simp only [center,ThreeBranchLegendreInfinityAlgebra318.center,parameter_eq,difference]

/-- The old short-Weierstrass translation cancels EXACTLY. The normalized
coordinate is (original t - first omitted-branch coordinate)/difference. -/
lemma finite_normalized_coordinate (i:Fin 4):
    mapOnRings i (ShortAffineJacobian318.x (A i) (B i)+algebraMap ℂ _
      (NormalizedLegendreProjectiveModel318.shift (PELOriginalOrderedCharacterCoordinate318.parameter i)))=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (difference i)⁻¹*
      FourRootAffineCoordinateRing318.coordinate branches none+
      algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (offset i):=by
  rw [map_add,AlgHom.commutes,finite_x,center_eq,map_add,map_mul]
  have hd:algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (difference i)⁻¹*
      algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (difference i)=1:=by
    rw [←map_mul,inv_mul_cancel₀ (difference_ne_zero i),map_one]
  simp only [offset,div_eq_mul_inv,map_mul,map_neg]
  linear_combination -algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches)
    (NormalizedLegendreProjectiveModel318.shift (PELOriginalOrderedCharacterCoordinate318.parameter i))*hd

lemma finite_square (i:Fin 4):FourRootGluedScheme318.finiteChart branches≫morphism i≫
    NormalizedLegendreSchemeProjection318.projection (PELOriginalOrderedCharacterCoordinate318.parameter i)=
    FourRootGluedScheme318.finiteChart branches≫FourRootProjectiveProjection318.projection branches≫
      (baseNormalization i).hom:=by
  rw [←Category.assoc,on_finite,finiteMap,Category.assoc,
    NormalizedLegendreSchemeProjection318.finite_chart,
    ←Category.assoc (FourRootGluedScheme318.finiteChart branches),
    FourRootProjectiveProjection318.finite_projection,Category.assoc,
    ProjectiveAffineCharts318.chart_naturality]
  unfold PELOriginalOrderedCharacterSchemeMaps318.morphism
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,map_add,map_mul,Polynomial.aeval_C]
    exact finite_normalized_coordinate i

/-- A full scheme equality over the actual original base. This identifies
the NORMALIZED projection, not only the earlier unnormalized targetTMap. -/
theorem whole_square (i:Fin 4):morphism i≫
    NormalizedLegendreSchemeProjection318.projection (PELOriginalOrderedCharacterCoordinate318.parameter i)=
    FourRootProjectiveProjection318.projection branches≫(baseNormalization i).hom:=by
  apply FourRootSchematicDensity318.ext branches branches_injective
    (ProjectiveJLine318.structureMap ℂ)
  · rw [Category.assoc,NormalizedLegendreSchemeProjection318.over_base,
      PELOriginalWholeCharacterMorphisms318.over_complex,Category.assoc,
      PELOriginalOrderedBaseSchemeNormalization318.over_complex,
      FourRootProjectiveProjection318.over_base]
  · exact finite_square i
end PELOriginalNormalizedBaseSchemeSquare318
