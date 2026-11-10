module
public import PELOriginalBoundedSeamCoordinate318
public import PELOriginalUnitTraceComparison318
public import ComplexCurveBoundedAffineLimit318
public section
noncomputable section
namespace PELOriginalConstructedSphereFilling318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELMaximalActualComplexDomain318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonOriginalPoints318 PELOriginalOpenDenseInterior318
open PELActualBoundarySixCorners318 PELActualEdgeHalfNeighborhood318
open PELOriginalConformalComparisonInputs318 PELOriginalBoundedSeamCoordinate318
open PELOriginalCompactConformalCore318 PELMaximalHalfOctagonBoundaryAction318
open PELOriginalMaximalSphere318 ComplexSphereCharts318 ReflectedDiskJoukowski318
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ) := sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := sphere_manifold
set_option maxHeartbeats 2600000

lemma interior_not_cornerOrbits {q:MaximalBase} (hq:q∈originalInterior) : q∉cornerOrbits := by
  rintro ⟨k,hk⟩
  exact boundary_not_originalInterior _ (corner_not_strict k) (hk.symm ▸ hq)

lemma corner_not_regular (i k:Fin 6) : ¬RegularEdge i (complexCorner k) := by
  intro h
  have hc:coordinates (complexCorner k)=corner k := by
    change coordinates (cutPoint ⟨corner k,corner_mem k⟩)=corner k
    rw [coordinates_halfPlane,cutPoint_coordinates]
  have h₀:=h.2.2 0
  have h₁:=h.2.2 1
  have h₂:=h.2.2 2
  have h₃:=h.2.2 3
  have h₄:=h.2.2 4
  have h₅:=h.2.2 5
  fin_cases i <;> fin_cases k <;>
    norm_num [slack,hc,corner] at h₀ h₁ h₂ h₃ h₄ h₅

@[expose] def reflectedCorner : Fin 6→Fin 6:=![5,4,3,2,1,0]
lemma reflected_corner (k:Fin 6) :
    reflectedCut ⟨corner k,corner_mem k⟩=
      (⟨corner (reflectedCorner k),corner_mem (reflectedCorner k)⟩:upperCut) := by
  apply Subtype.ext
  fin_cases k <;> norm_num [reflectedCut,corner,reflectedCorner]

/-- Actual full-normalizer fibers cannot identify a regular original edge
point with a corner. Reflection permutes the literal six corners. -/
lemma regular_not_cornerOrbits (P:upperCut) (i:Fin 6) (hi:RegularEdge i (cutPoint P:ℂ)) :
    cutProjection P∉cornerOrbits := by
  rintro ⟨k,hk⟩
  rcases (cutProjection_fibers ⟨corner k,corner_mem k⟩ P).mp hk with he|⟨_,he⟩
  · rw [←he] at hi
    exact corner_not_regular i k hi
  · rw [reflected_corner] at he
    rw [he] at hi
    exact corner_not_regular i (reflectedCorner k) hi

/-- The actual finite punctures now have CONSTRUCTED affine limits.
Only punctured holomorphy and the same interior/regular-edge formulas
remain inputs; no value or continuity at a corner is supplied. -/
theorem exists_original_holomorphic_filling
    (F:MaximalBase→OnePoint ℂ)
    (hF:∀q∉cornerOrbits,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=joukowski w) :
    ∃G:MaximalBase→OnePoint ℂ,ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G ∧
      (∀q∉cornerOrbits,G q=F q) ∧ InteriorAgreement G e ∧
      (∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
        ∃w:ℂ,‖w‖=1 ∧ G (cutProjection P)=joukowski w) := by
  have hbound:∀p∈cornerOrbits,∀ᶠq in 𝓝[≠] p,
      F q∈affine.source ∧ ‖affine (F q)‖≤3 := by
    intro p hp
    have hnb:= (seamNeighborhood_open e hs ht).mem_nhds
      (cornerOrbits_in_seamNeighborhood e hs ht hp)
    have hfinite:(cornerOrbits\{p}).Finite:=cornerOrbits_finite.subset diff_subset
    have havoid:(cornerOrbits\{p})ᶜ∈𝓝 p:=hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnb,
      eventually_nhdsWithin_of_eventually_nhds havoid,self_mem_nhdsWithin] with q hq havoidq hqp
    have hn:q∉cornerOrbits:=fun h=>havoidq ⟨h,hqp⟩
    exact original_seam_chart_bound F e hs ht ha hedge q hq hn
  obtain ⟨G,hG,hagree,hfinite⟩:=ComplexCurveBoundedAffineLimit318.exists_holomorphic_filling
    F cornerOrbits cornerOrbits_finite hF 3 hbound
  refine ⟨G,hG,hagree,?_,?_⟩
  · intro τ hτ
    rw [hagree _ (interior_not_cornerOrbits ⟨τ,hτ,rfl⟩)]
    exact ha τ hτ
  · intro P i hi
    obtain ⟨w,hw,hFw⟩:=hedge P i hi
    exact ⟨w,hw,(hagree _ (regular_not_cornerOrbits P i hi)).trans hFw⟩

/-- End-to-end same-original-atlas sphere comparison from the GENUINE
punctured arithmetic descent map. Vertex filling, global continuity,
all-boundary exclusion, global injectivity/surjectivity, and inverse
holomorphy are conclusions, not additional hypotheses. -/
theorem exists_original_biholomorphic_sphere
    (F:MaximalBase→OnePoint ℂ)
    (hF:∀q∉cornerOrbits,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F q)
    (e:OpenPartialHomeomorph ℂ ℂ) (hs:e.source=openDomain)
    (ht:e.target=Metric.ball 0 1) (ha:InteriorAgreement F e)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=joukowski w) :
    ∃H:MaximalBase≃ₜOnePoint ℂ,
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      (∀q∉cornerOrbits,H q=F q) ∧ InteriorAgreement H e := by
  obtain ⟨G,hG,hagree,hGa,hGe⟩:=exists_original_holomorphic_filling F hF e hs ht ha hedge
  refine ⟨PELOriginalUnitTraceComparison318.comparison G hG e hs ht hGa hGe,?_,?_,hagree,hGa⟩
  · exact (PELOriginalUnitTraceComparison318.comparison_biholomorphic G hG e hs ht hGa hGe).1
  · exact (PELOriginalUnitTraceComparison318.comparison_biholomorphic G hG e hs ht hGa hGe).2
end PELOriginalConstructedSphereFilling318
