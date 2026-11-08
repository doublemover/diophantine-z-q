module
public import ProjectiveSwapCharts318
public import FifthCharacterShortCoordinates318
public import WeierstrassXStructure318
public section
noncomputable section
namespace FifthTargetParameter318
open AlgebraicGeometry CategoryTheory Polynomial
open FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Exact P1 automorphism taking short x to the original t=m/(x-k). -/
@[expose] def parameterIso:ProjectiveJLine318.scheme ℚ≅ProjectiveJLine318.scheme ℚ:=
  (ProjectiveAffineLine318.iso ℚ xScale⁻¹ (-((xScale⁻¹:ℚˣ):ℚ)*shift)).trans
    (ProjectiveSwap318.iso ℚ)
@[reassoc] theorem parameterIso_over_Q:parameterIso.hom≫ProjectiveJLine318.structureMap ℚ=
    ProjectiveJLine318.structureMap ℚ:=by
  change (ProjectiveAffineLine318.map ℚ xScale⁻¹ (-((xScale⁻¹:ℚˣ):ℚ)*shift)≫ProjectiveSwap318.map ℚ)≫_=_
  rw [Category.assoc,ProjectiveSwapCharts318.over_base,ProjectiveAffineCharts318.map_over_base]
@[expose] def normalization:ℚ[X]:=C ((xScale⁻¹:ℚˣ):ℚ)*X+C (-((xScale⁻¹:ℚˣ):ℚ)*shift)
/-- On the entire finite short-x chart, the reciprocal original parameter
is (x-k)/m. The chart exchange is an actual P1 isomorphism. -/
@[reassoc] theorem chart_formula:JLineAtlas318.chart ℚ 1≫parameterIso.hom=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval normalization).toRingHom)≫JLineAtlas318.chart ℚ 0:=by
  change JLineAtlas318.chart ℚ 1≫(ProjectiveAffineLine318.map ℚ xScale⁻¹ (-((xScale⁻¹:ℚˣ):ℚ)*shift)≫
    ProjectiveSwap318.map ℚ)=_
  rw [←Category.assoc,ProjectiveAffineCharts318.chart_naturality,Category.assoc,ProjectiveSwapCharts318.chart_one]
  rfl
@[expose] def map:WeierstrassGluing318.scheme A B⟶ProjectiveJLine318.scheme ℚ:=
  WeierstrassXProjection318.xMap A B≫parameterIso.hom
@[reassoc] theorem over_Q:map≫ProjectiveJLine318.structureMap ℚ=WeierstrassGluing318.structureMap A B:=by
  rw [map,Category.assoc,parameterIso_over_Q,WeierstrassXStructure318.xMap_over_base]
@[expose] def reciprocalParameter:ShortAffineJacobian318.Ring A B:=
  algebraMap ℚ _ ((xScale⁻¹:ℚˣ):ℚ)*ShortAffineJacobian318.x A B+
    algebraMap ℚ _ (-((xScale⁻¹:ℚˣ):ℚ)*shift)
@[reassoc] theorem finite_restriction:WeierstrassGluing318.finiteChart A B≫map=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval reciprocalParameter).toRingHom)≫JLineAtlas318.chart ℚ 0:=by
  rw [map,←Category.assoc,WeierstrassXProjection318.finiteChart_xMap]
  unfold WeierstrassXProjection318.finiteProjection
  rw [Category.assoc,chart_formula,←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
    simp only [normalization,map_add,map_mul,Polynomial.aeval_C,Polynomial.aeval_X,reciprocalParameter]
end FifthTargetParameter318
