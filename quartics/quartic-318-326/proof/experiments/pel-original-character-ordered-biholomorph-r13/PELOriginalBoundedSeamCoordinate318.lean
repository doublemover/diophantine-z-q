module
public import PELOriginalCompactConformalCore318
public import PELOriginalBoundaryClosedPropagation318
public import BoundedVertexExtension318
public section
noncomputable section
namespace PELOriginalBoundedSeamCoordinate318
open Set Metric
open scoped OnePoint
open PELOriginalCompactConformalCore318 PELOriginalMaximalQuotient318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonShape318
open PELActualBoundarySixCorners318 PELActualEdgeHalfNeighborhood318
open PELOriginalConformalComparisonInputs318 ReflectedDiskJoukowski318

/-- The finite exceptional arithmetic set is the actual image of the six
cut corners. No claim is made that these are six distinct branch values. -/
@[expose] def cornerOrbits : Set MaximalBase :=
  range (fun k:Fin 6=>cutProjection ⟨corner k,corner_mem k⟩)
lemma cornerOrbits_finite : cornerOrbits.Finite := Set.finite_range _

lemma corner_not_strict (k:Fin 6) :
    (upperCutCenter ⟨corner k,corner_mem k⟩).val∉strictPolygon := by
  fin_cases k <;> norm_num [upperCutCenter,centerHomeomorph,corner,strictPolygon]

lemma cornerOrbits_in_seamNeighborhood (e:OpenPartialHomeomorph ℂ ℂ)
    (hs:e.source=openDomain) (ht:e.target=ball 0 1) :
    cornerOrbits⊆seamNeighborhood e hs ht := by
  rintro q ⟨k,rfl⟩
  exact boundary_in_seamNeighborhood e hs ht _ (corner_not_strict k)

/-- On the entire punctured seam neighborhood, the SAME actual descended
formula lands in one bounded AFFINE target chart. Its bound comes from
|f|>1/2 inside and the constructed unit traces on regular edges, never
from compactness of the sphere. No continuity at a corner is required. -/
theorem original_seam_affine_bound (F:MaximalBase→OnePoint ℂ)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=joukowski w)
    (q:MaximalBase) (hq:q∈seamNeighborhood e hs ht) (hn:q∉cornerOrbits) :
    ∃w:ℂ,‖w‖≤3 ∧ F q=(w:OnePoint ℂ) := by
  obtain ⟨P,rfl⟩:=PELMaximalHalfOctagonBoundaryAction318.cutProjection_surjective q
  by_cases hi:(cutPoint P:ℂ)∈openDomain
  · have hlo: (1/2:ℝ)<‖e (cutPoint P)‖:=interior_modulus_lower e hs ht _ hi hq
    have hhi:‖e (cutPoint P)‖<1:=by
      have h:=e.map_source (hs.symm ▸ hi)
      rw [ht,mem_ball,dist_zero_right] at h
      exact h
    have hnz:e (cutPoint P)≠0:=by
      intro he
      rw [he,norm_zero] at hlo
      norm_num at hlo
    refine ⟨e (cutPoint P)-(e (cutPoint P))⁻¹,
      BoundedVertexExtension318.joukowski_bound _ hlo.le hhi.le,?_⟩
    rw [ha _ hi]
    exact if_neg hnz
  · rcases closed_boundary_regular_or_corner (show (cutPoint P:ℂ)∈closedDomain from ⟨P,rfl⟩) hi
      with ⟨i,hreg⟩|⟨k,hk⟩
    · obtain ⟨w,hw,hFw⟩:=hedge P i hreg
      have hnz:w≠0:=by intro he;rw [he,norm_zero] at hw;norm_num at hw
      refine ⟨w-w⁻¹,BoundedVertexExtension318.joukowski_bound w (by rw [hw];norm_num) hw.le,?_⟩
      rw [hFw]
      exact if_neg hnz
    · exfalso
      apply hn
      refine ⟨k,?_⟩
      apply congrArg maximalProjection
      apply Subtype.ext
      exact hk

/-- Both chart access and its exact norm estimate are now consequences.
This is directly usable by original-chart isolated-point removability. -/
theorem original_seam_chart_bound (F:MaximalBase→OnePoint ℂ)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=joukowski w)
    (q:MaximalBase) (hq:q∈seamNeighborhood e hs ht) (hn:q∉cornerOrbits) :
    F q∈ComplexSphereCharts318.affine.source ∧ ‖ComplexSphereCharts318.affine (F q)‖≤3 := by
  obtain ⟨w,hw,hFw⟩:=original_seam_affine_bound F e hs ht ha hedge q hq hn
  rw [hFw]
  exact ⟨ComplexSphereCharts318.affine_mem w,by rw [ComplexSphereCharts318.affine_coe];exact hw⟩
end PELOriginalBoundedSeamCoordinate318
