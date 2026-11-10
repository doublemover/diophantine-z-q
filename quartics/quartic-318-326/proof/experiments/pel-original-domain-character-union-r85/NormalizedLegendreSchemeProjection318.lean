module
public import NormalizedLegendreProjectiveModel318
public import ProjectiveAffineCharts318
public import WeierstrassXStructure318
public section
noncomputable section
namespace NormalizedLegendreSchemeProjection318
open AlgebraicGeometry CategoryTheory Polynomial
open NormalizedLegendreProjectiveModel318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (l:ℂ)

/-- Genuine full Scheme morphism with LEGENDRE t coordinate, not the
shifted native Weierstrass x. The final affine change is the old Proj map. -/
@[expose] def projection : model l ⟶ ProjectiveJLine318.scheme ℂ:=
  nativeXMap l ≫ ProjectiveAffineLine318.map ℂ 1 (shift l)

lemma over_base : projection l ≫ ProjectiveJLine318.structureMap ℂ=structure l := by
  rw [projection,Category.assoc,ProjectiveAffineCharts318.map_over_base,
    WeierstrassXStructure318.xMap_over_base]

/-- The actual finite-chart map is evaluation at original x+shift, as
an equality of FULL Scheme morphisms, not just rational-point values. -/
lemma finite_chart : WeierstrassGluing318.finiteChart (A l) (B l) ≫ projection l=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℂ)
      (ShortAffineJacobian318.x (A l) (B l)+algebraMap ℂ _ (shift l))).toRingHom) ≫
      JLineAtlas318.chart ℂ 1 := by
  rw [projection,←Category.assoc,WeierstrassXProjection318.finiteChart_xMap]
  rw [WeierstrassXProjection318.finiteProjection,Category.assoc,
    ProjectiveAffineCharts318.chart_naturality,←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,map_add,map_mul,Polynomial.aeval_C,
      Units.val_one,map_one,one_mul]

/-- Properness applies to this SAME normalized projection, by the actual
structure-map factorization and separatedness of projective line. -/
theorem proper : IsProper (projection l):=by
  haveI:IsProper (projection l≫ProjectiveJLine318.structureMap ℂ):=by
    rw [over_base]
    exact NormalizedLegendreProjectiveModel318.proper l
  exact IsProper.of_comp _ (ProjectiveJLine318.structureMap ℂ)
end NormalizedLegendreSchemeProjection318
