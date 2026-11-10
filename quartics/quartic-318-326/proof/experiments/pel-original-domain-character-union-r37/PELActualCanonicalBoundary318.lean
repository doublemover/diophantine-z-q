module
public import PELActualBoundarySixCorners318
public import PELActualDomainClosure318
public import CanonicalBoundaryTrace318
public section
noncomputable section
namespace PELActualCanonicalBoundary318
open Set Filter Metric
open scoped Topology ComplexConjugate OnePoint
open PELMaximalActualComplexDomain318 PELActualEdgeHalfNeighborhood318
open PELActualBoundarySixCorners318 PELActualDomainClosure318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonBoundaryAction318
set_option maxHeartbeats 3000000

@[expose] def puncturedClosed : Set ℂ := closedDomain\corners
@[expose] def trace (f:ℂ→ℂ) : ℂ→ℂ := CanonicalBoundaryTrace318.value openDomain f
@[expose] def J (z:ℂ) : ℂ := -conj z

theorem J_open (z:ℂ) : J z∈openDomain ↔ z∈openDomain := by
  have forward (w:ℂ) (hw:w∈openDomain) : J w∈openDomain := by
    have hi:0<w.im := hw.1
    have hcoords:coordinates (J w)=(-(coordinates w).1,(coordinates w).2) :=
      mirror_coordinates ⟨w,hi⟩
    obtain ⟨him,h⟩ := (original_domain_iff w).mp hw
    apply (original_domain_iff (J w)).mpr
    refine ⟨by simpa [J] using him,?_⟩
    have h₀:=h 0;have h₁:=h 1;have h₂:=h 2;have h₃:=h 3;have h₄:=h 4;have h₅:=h 5
    norm_num [slack] at h₀ h₁ h₂ h₃ h₄ h₅
    intro i
    fin_cases i <;> norm_num [slack,hcoords] <;> linarith
  constructor
  · intro h
    simpa [J] using forward (J z) h
  · exact forward z

@[expose] def flip : Fin 6→Fin 6 := ![5,4,3,2,1,0]

theorem corner_flip (k:Fin 6) : complexCorner (flip k)=J (complexCorner k) := by
  have hp:(⟨corner (flip k),corner_mem (flip k)⟩:upperCut)=
      reflectedCut ⟨corner k,corner_mem k⟩ := by
    apply Subtype.ext
    fin_cases k <;> norm_num [corner,flip,reflectedCut]
  change (cutPoint ⟨corner (flip k),corner_mem (flip k)⟩:ℂ)=_
  rw [hp,cutPoint_reflection]
  rfl

theorem J_corners (z:ℂ) : J z∈corners ↔ z∈corners := by
  have forward (w:ℂ) (hw:w∈corners) : J w∈corners := by
    obtain ⟨k,rfl⟩ := hw
    exact ⟨flip k,corner_flip k⟩
  constructor
  · intro h
    simpa [J] using forward (J z) h
  · exact forward z

theorem J_puncturedClosed (z:ℂ) : J z∈puncturedClosed ↔ z∈puncturedClosed := by
  change J z∈closedDomain ∧ J z∉corners ↔ z∈closedDomain ∧ z∉corners
  rw [show J z∈closedDomain ↔ z∈closedDomain from closedDomain_reflection z,J_corners]

section Trace
variable (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
include hf hfa

/-- The actual edge construction plus ordinary interior analyticity
supplies a germ at EVERY point of the punctured closed half-cut. -/
theorem noncorner_germ {z:ℂ} (hz:z∈puncturedClosed) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ F=ᶠ[𝓝[openDomain] z] f := by
  by_cases hi:z∈openDomain
  · exact ⟨f,hfa z hi,Filter.EventuallyEq.rfl⟩
  · have hb:z∈frontier openDomain := by rw [actual_frontier];exact ⟨hz.1,hi⟩
    obtain ⟨F,hF,he,_⟩ := actual_frontier_extension_except_corners disk f hf hfa hb hz.2
    exact ⟨F,hF,he⟩

theorem trace_limit {z:ℂ} (hz:z∈puncturedClosed) :
    Tendsto f (𝓝[openDomain] z) (𝓝 (trace f z)) := by
  obtain ⟨F,hF,he⟩ := noncorner_germ disk f hf hfa hz
  have hc:z∈closure openDomain := by rw [closure_openDomain];exact hz.1
  have ht:=CanonicalBoundaryTrace318.limit_from_germ openDomain f F hF.continuousAt he
  rw [show trace f z=F z from CanonicalBoundaryTrace318.value_eq_of_limit openDomain f hc ht]
  exact ht

theorem trace_continuous : ContinuousOn (trace f) puncturedClosed := by
  intro z hz
  obtain ⟨F,hF,he⟩ := noncorner_germ disk f hf hfa hz
  have hc:z∈closure openDomain := by rw [closure_openDomain];exact hz.1
  apply (CanonicalBoundaryTrace318.canonical_continuousWithin openDomain f F hc hF he).mono
  intro w hw
  rw [closure_openDomain]
  exact hw.1

theorem trace_on_interior {z:ℂ} (hz:z∈openDomain) : trace f z=f z :=
  CanonicalBoundaryTrace318.value_eq_on_open openDomain f hz (hfa z hz).continuousAt.continuousWithinAt

theorem trace_unit_on_boundary {z:ℂ} (hz:z∈puncturedClosed) (hi:z∉openDomain) : ‖trace f z‖=1 := by
  have hb:z∈frontier openDomain := by rw [actual_frontier];exact ⟨hz.1,hi⟩
  obtain ⟨F,hF,he,hunit⟩ := actual_frontier_extension_except_corners disk f hf hfa hb hz.2
  have hc:z∈closure openDomain := by rw [closure_openDomain];exact hz.1
  rw [show trace f z=F z from CanonicalBoundaryTrace318.value_eq_of_limit openDomain f hc
    (CanonicalBoundaryTrace318.limit_from_germ openDomain f F hF.continuousAt he)]
  exact hunit

/-- The original normalized interior mirror identity passes to the
canonical edge traces, independent of choices of local extensions. -/
theorem trace_mirror (hmirror:∀z∈openDomain,f (J z)=J (f z))
    {z:ℂ} (hz:z∈puncturedClosed) : trace f (J z)=J (trace f z) := by
  have hc:z∈closure openDomain := by rw [closure_openDomain];exact hz.1
  have hσ:J z∈closure openDomain := by
    rw [closure_openDomain]
    exact ((J_puncturedClosed z).mpr hz).1
  exact CanonicalBoundaryTrace318.canonical_reflection openDomain J_open f hmirror hc hσ
    (trace_limit disk f hf hfa hz)

/-- Whole paired-edge trace equality for the actual sphere coordinate.
The paired source points are the original mirror points; boundary unit
norm is proved above, rather than assumed as a gluing rule. -/
theorem boundary_sphere_trace_mirror (hmirror:∀z∈openDomain,f (J z)=J (f z))
    {z:ℂ} (hz:z∈puncturedClosed) (hi:z∉openDomain) :
    ReflectedDiskJoukowski318.joukowski (trace f (J z))=
      ReflectedDiskJoukowski318.joukowski (trace f z) := by
  rw [trace_mirror disk f hf hfa hmirror hz]
  apply Eq.symm
  apply (ReflectedDiskJoukowski318.sphere_fibers _ _).mpr
  right
  have hu:=trace_unit_on_boundary disk f hf hfa hz hi
  change trace f z*(-conj (trace f z))= -1
  rw [mul_neg,Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
  norm_num
end Trace
end PELActualCanonicalBoundary318
