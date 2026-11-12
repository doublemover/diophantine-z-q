module
public import PELOriginalLocalHolomorphicDescent318
public section
noncomputable section
namespace PELActualPuncturedHolomorphy318
open Set Filter Topology
open scoped Manifold ContDiff OnePoint
open QuaternionicJointPeriodTopology318 PELMaximalActualComplexDomain318
open PELActualCanonicalBoundary318 PELActualBoundarySixCorners318
open PELActualPuncturedQuotientMap318 PELActualAmbientProjection318 PELActualArithmeticCollar318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELStabilizerLocusInvariant318 PELOriginalFiniteBranchImage318
open PELPrincipalBaseHolomorphy318 ComplexSphereCharts318
set_option maxHeartbeats 3200000
local instance : ChartedSpace ℂ HalfPlane:=halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane:=halfPlane_manifold
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

@[expose] def exceptions : Set MaximalBase:=cornerImages∪branchImage

theorem exceptions_finite : exceptions.Finite:=
  cornerImages_finite.union original_branch_image_finite

section Conformal
variable (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    (hmirror:∀z∈openDomain,f (J z)=J (f z))
include hf hfa hmirror

/-- Every noncorner original cut representative has an actual sphere-
valued holomorphic pullback germ, including ALL six genuine edge collars. -/
theorem ambient_holomorphicAt {z:ℂ} (hz:z∈closedDomain)
    (hq:ambientProjection z∈regularBase) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (ambientMap f) z := by
  by_cases hi:z∈openDomain
  · have hJ:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y=>ReflectedDiskJoukowski318.joukowski (f y)) z :=
      (ComplexSphereJoukowski318.joukowski_holomorphic (f z)).comp z
        (contMDiffAt_iff_contDiffAt.mpr (hfa z hi).contDiffAt)
    apply hJ.congr_of_eventuallyEq
    have hsafe:∀ᶠy in 𝓝 z,ambientProjection y∈regularBase :=
      (ambientProjection_continuousAt hi.1).eventually (regularBase_open.mem_nhds hq)
    filter_upwards [openDomain_open.mem_nhds hi,hsafe] with y hy hs
    exact ambientMap_interior disk f hf hfa hmirror hy hs
  · have hn:z∉corners := by
      obtain ⟨P,hP⟩:=hz
      have hp:cutProjection P∈regularBase := by
        simpa only [←hP,ambientProjection_upper] using hq
      have hnon:=original_noncorner (⟨P,hp⟩:regularCut)
      simpa only [hP] using hnon.2
    rcases closed_boundary_regular_or_corner hz hi with ⟨i,he⟩|hc
    · obtain ⟨F,hF,_,hagree⟩:=original_whole_collar disk f hf hfa hmirror he hq
      have hJ:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
          (fun y=>ReflectedDiskJoukowski318.joukowski (F y)) z :=
        (ComplexSphereJoukowski318.joukowski_holomorphic (F z)).comp z
          (contMDiffAt_iff_contDiffAt.mpr hF.contDiffAt)
      exact hJ.congr_of_eventuallyEq hagree
    · exact False.elim (hn hc)

/-- The pullback germ lives on the ORIGINAL upper-half-plane complex
manifold, rather than a new chart transported from the desired target. -/
theorem upper_holomorphicAt (P:upperCut) (hq:cutProjection P∈regularBase) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (totalMap f ∘ maximalProjection) (cutPoint P) := by
  have ha:=ambient_holomorphicAt disk f hf hfa hmirror
    (show (cutPoint P:ℂ)∈closedDomain from ⟨P,rfl⟩)
    (show ambientProjection (cutPoint P)∈regularBase from by rw [ambientProjection_upper];exact hq)
  apply (ha.comp (cutPoint P) (inclusion_holomorphic (cutPoint P))).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun τ=>by
    change totalMap f (maximalProjection τ)=totalMap f (ambientProjection τ)
    rw [ambientProjection_upper])

/-- Actual cut coverage plus both unchanged quotient atlases now gives
holomorphic descent away from an EXPLICIT finite union. No local sheet,
full-collar equality, boundary trace or genus assumption remains as input. -/
theorem actual_punctured_holomorphic (q:MaximalBase) (hq:q∉exceptions) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (totalMap f) q := by
  obtain ⟨P,rfl⟩:=PELMaximalHalfOctagonBoundaryAction318.cutProjection_surjective q
  have hcorner:cutProjection P∈regularBase:=fun h=>hq (Or.inl h)
  have hbranch:cutProjection P∉branchImage:=fun h=>hq (Or.inr h)
  exact PELOriginalLocalHolomorphicDescent318.upper_regular_local (totalMap f)
    (cutPoint P) hbranch (upper_holomorphicAt disk f hf hfa hmirror P hcorner)
end Conformal
end PELActualPuncturedHolomorphy318
