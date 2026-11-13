module
public import FourRootProjectiveProjection318
public import PELOriginalContactSchemePoints318
public import ProjectiveLineActualAutomorphismPoints318
public import FourRootSchemeSignAction318
public section
noncomputable section
namespace FourRootProjectivePointComparison318
open AlgebraicGeometry CategoryTheory Polynomial
open FourRootNormalizedPointCharts318 FourRootCompletedSchemePoints318
open FourRootSchemeChartInputs318 FourRootProjectiveProjection318
open scoped OnePoint
variable (b:Fin 4→ℂ)
@[expose] def projectionPoint (p:SchemePoints b):ProjectiveLineComplexSchemePoints318.SchemePoints:=
  ⟨p.val≫FourRootProjectiveProjection318.projection b,by
    rw [Category.assoc,over_base]
    exact p.property⟩
lemma finite_point_projection (p:FinitePoints b):
    projectionPoint b (finitePoint b p)=ProjectiveLineComplexSchemePoints318.chartPoint 1 p.val.1:=by
  apply Subtype.ext
  change (finiteInput b _≫FourRootProjectiveProjection318.projection b)=_
  rw [finiteInput,Category.assoc,finite_projection,←Category.assoc,←Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c;simp
  · simp [FourRootAffineCoordinateRing318.pointEquiv]
lemma infinity_point_projection (s:InfinitySigns):
    projectionPoint b (infinityPoint b (center b s))=
      ProjectiveLineComplexSchemePoints318.chartPoint 0 0:=by
  apply Subtype.ext
  change infinityInput b _≫FourRootProjectiveProjection318.projection b=_
  rw [infinityInput,Category.assoc,infinity_projection,←Category.assoc,←Spec.map_comp]
  have he:((FourRootInfinityCoordinateRing318.pointEquiv b).symm (center b s)).comp
      (infinityCoordinate b)=Polynomial.aeval (0:ℂ):=by
    apply Polynomial.algHom_ext
    simp [infinityCoordinate,center,FourRootInfinityCoordinateRing318.pointEquiv]
  have hh:=congrArg (fun f:Polynomial ℂ→ₐ[ℂ]ℂ=>Spec.map (CommRingCat.ofHom f.toRingHom)) he
  rw [hh]
  exact ProjectiveLineActualAutomorphismPoints318.affine_infinity 1 (b 0)

/-- The Scheme projection has exactly the ORIGINAL t-value on every
finite point and genuine projective infinity at each of the eight signs. -/
theorem completed_projection (p:Completed b):
    projectionPoint b (schemePointEquiv b p)=
      ProjectiveLineComplexSchemePoints318.spherePoint
        (FourRootNormalizedPointCharts318.projection b p):=by
  rcases p with p|s
  · exact finite_point_projection b p
  · exact infinity_point_projection b s

/-- Exact original marked base map, now expressed by postcomposition of
genuine Scheme-valued points with the actual projective Scheme morphism. -/
theorem original_projection (p:PELUnlevelledComplexBase318.UnlevelledBase):
    projectionPoint PELOriginalCommonContactBase318.branches
      (PELOriginalContactSchemePoints318.comparison p)=
    ProjectiveLineComplexSchemePoints318.spherePoint
      (PELOriginalContactBranchSquare318.normalizedMap p):=by
  change projectionPoint _ (schemePointEquiv _
    (PELOriginalCompletedContactBiholomorph318.comparison p))=_
  rw [completed_projection,PELOriginalCompletedContactBiholomorph318.actual_projection]

/-- The whole Scheme deck action preserves the specified projective base,
not just its complex point values. -/
theorem deck_over_projective (g:FourBinaryCharacters318.Group):
    FourRootSchemeSignAction318.action b g≫FourRootProjectiveProjection318.projection b=
      FourRootProjectiveProjection318.projection b:=by
  have hc:FourRootSchemeSignAction318.action b g≫centeredProjection b=centeredProjection b:=by
    apply FourRootGluedScheme318.hom_ext
    · rw [FourRootSchemeSignAction318.finite_action_assoc,finite_centered,finite_centered]
      unfold FourRootSchemeSignAction318.finiteMap finiteProjection
      rw [←Category.assoc,←Spec.map_comp]
      congr 1
      congr 1
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro c;exact (FourRootCoordinateRingSigns318.finiteEnd b g).commutes c
      · simp [finiteCoordinate,FourRootCoordinateRingSigns318.finite_base]
    · rw [FourRootSchemeSignAction318.infinity_action_assoc,infinity_centered,infinity_centered]
      unfold FourRootSchemeSignAction318.infinityMap infinityProjection
      rw [←Category.assoc,←Spec.map_comp]
      congr 1
      congr 1
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro c;exact (FourRootCoordinateRingSigns318.infinityEnd b g).commutes c
      · simp [infinityCoordinate,FourRootCoordinateRingSigns318.infinity_parameter,
          mul_pow,←map_pow,FourBinaryCharacters318.coordinate_square]
  rw [FourRootProjectiveProjection318.projection,←Category.assoc,hc]
end FourRootProjectivePointComparison318
