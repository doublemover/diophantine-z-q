module

public import SelectedActualComplexGenericCompactNormal318
public import SelectedActualAbelFiniteNormalChartDVR318

public section

noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualAbelFiniteNormalChartDVR318

namespace SelectedActualComplexCompactOriginalDVR318

variable (K : Type) [Field K] [Algebra JField K]

/-- The actual affine structure map of the compact normalized chart,
with the base chart sections identified with the literal C[T]. -/
def chartCoefficient (i : Fin 2) : ℂ[X] →+* chartRing K i :=
  ((NormalizationChart318.targetSections (JLineAtlas318.chart ℂ i)).inv ≫
    (modelMap K).app (targetCover i).1).hom

variable [aK : Algebra ℂ K] [hTower : IsScalarTower ℂ JField K]
  [hFin : FiniteDimensional JField K] [hSep : Algebra.IsSeparable JField K]

include aK hTower hFin hSep in
theorem chartCoefficient_finite (i : Fin 2) : (chartCoefficient K i).Finite := by
  letI : IsFinite (modelMap K) := model_finite K
  unfold chartCoefficient
  apply RingHom.finite_respectsIso.2
    (e := (NormalizationChart318.targetSections (JLineAtlas318.chart ℂ i)).symm.commRingCatIsoToRingEquiv)
  exact (modelMap K).finite_app (targetCover i).1 (targetCover i).2

include aK hTower hFin hSep in
/-- Every closed (nongeneric) point on the genuine complex normal
compact scheme has its *actual* DVR stalk, over these two fixed finite
structural maps. The field K is not reselected across the two charts. -/
theorem complex_normalization_stalk_dvr (x : model K)
    (hx : x ≠ genericPoint (model K)) :
    IsDiscreteValuationRing ((model K).presheaf.stalk x) := by
  let U : Fin 2 → (model K).Opens := fun i => (sourceCover K i).1
  letI (i : Fin 2) : Algebra ℂ[X] Γ(model K, U i) := (chartCoefficient K i).toAlgebra
  letI (i : Fin 2) : Module.Finite ℂ[X] Γ(model K, U i) := RingHom.finite_algebraMap.mp (chartCoefficient_finite K i)
  have hCover : (⊤ : (model K).Opens) ≤ iSup U := (sourceCover_covers K).symm.le
  exact original_stalk_isDVR_from_two_charts ℂ (model K) U
    (fun i => (sourceCover K i).2) hCover (fun i => (chart_domain_normal K i).2) x hx

end SelectedActualComplexCompactOriginalDVR318

#print axioms SelectedActualComplexCompactOriginalDVR318.chartCoefficient_finite
#print axioms SelectedActualComplexCompactOriginalDVR318.complex_normalization_stalk_dvr
