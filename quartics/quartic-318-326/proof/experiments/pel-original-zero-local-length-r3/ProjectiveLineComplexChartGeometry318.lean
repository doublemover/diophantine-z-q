module
public import JLineOverlap318
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
namespace ProjectiveLineComplexChartGeometry318
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1200000

/-- The actual complex projective-line chart overlap, on the SAME Proj
scheme, not a one-point compactification substituted for a scheme. -/
theorem chart_zero_preimage_one :
    JLineAtlas318.chart ℂ 0 ⁻¹ᵁ (JLineAtlas318.chart ℂ 1).opensRange=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial ℂ) := by
  rw [JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading ℂ)
    (isHomogeneous_X ℂ (0:Fin 2)) (by omega)
    (isHomogeneous_X ℂ (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv ℂ 0)
    (Away.isLocalizationElem (isHomogeneous_X ℂ (0:Fin 2))
      (isHomogeneous_X ℂ (1:Fin 2))))=_
  have h:Away.isLocalizationElem (isHomogeneous_X ℂ (0:Fin 2))
      (isHomogeneous_X ℂ (1:Fin 2))=
      (JLineAtlas318.chartEquiv ℂ 0).symm Polynomial.X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

/-- Field-valued points factor through one of the actual TWO polynomial
open charts, because the source field spectrum has exactly one point. -/
theorem field_chart_cases
    (f:Spec (CommRingCat.of ℂ) ⟶ ProjectiveJLine318.scheme ℂ) :
    ∃j:Fin 2,∃a:Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)),
      a ≫ JLineAtlas318.chart ℂ j=f := by
  have hp:f default∈(⊤:(ProjectiveJLine318.scheme ℂ).Opens):=trivial
  rw [←JLineAtlas318.standard_opens_cover ℂ,TopologicalSpace.Opens.mem_iSup] at hp
  obtain ⟨j,hj⟩:=hp
  rw [←JLineAtlas318.chart_range] at hj
  have h:Set.range f⊆Set.range (JLineAtlas318.chart ℂ j):=by
    rintro _ ⟨p,rfl⟩
    obtain ⟨a,ha⟩:=hj
    exact ⟨a,ha.trans (congrArg f (Subsingleton.elim default p))⟩
  exact ⟨j,IsOpenImmersion.lift _ f h,IsOpenImmersion.lift_fac _ _ h⟩
end ProjectiveLineComplexChartGeometry318
