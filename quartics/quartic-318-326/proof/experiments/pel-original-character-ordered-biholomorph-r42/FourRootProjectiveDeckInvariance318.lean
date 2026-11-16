module
public import PELOriginalNormalizedBaseSchemeSquare318
public section
noncomputable section
namespace FourRootProjectiveDeckInvariance318
open AlgebraicGeometry CategoryTheory Polynomial
open FourRootGluedScheme318 FourRootSchemeSignAction318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (g:FourBinaryCharacters318.Group)

lemma finite_projection_invariant:
    finiteMap b g≫finiteChart b≫FourRootProjectiveProjection318.projection b=
      finiteChart b≫FourRootProjectiveProjection318.projection b:=by
  simp only [FourRootProjectiveProjection318.finite_projection]
  unfold finiteMap
  rw [←Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_C,AlgHom.commutes]
  · simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
      AlgHom.coe_toRingHom,Polynomial.aeval_X,FourRootCoordinateRingSigns318.finite_base]

include hb in
/-- All original sign labels preserve the same unshifted whole projective
base map, including the actual normalized infinity chart. -/
theorem whole_projection_invariant:action b g≫FourRootProjectiveProjection318.projection b=
    FourRootProjectiveProjection318.projection b:=by
  apply FourRootSchematicDensity318.ext b hb (ProjectiveJLine318.structureMap ℂ)
  · rw [Category.assoc,FourRootProjectiveProjection318.over_base,over_base]
  · rw [←Category.assoc,finite_action,Category.assoc]
    exact finite_projection_invariant b g
end FourRootProjectiveDeckInvariance318
