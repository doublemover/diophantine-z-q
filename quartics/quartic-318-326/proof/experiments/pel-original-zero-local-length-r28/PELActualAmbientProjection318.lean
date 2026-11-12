module
public import PELActualPuncturedQuotientMap318
public section
noncomputable section
namespace PELActualAmbientProjection318
open Set Filter
open scoped Topology OnePoint
open QuaternionicJointPeriodTopology318
open PELMaximalActualComplexDomain318 PELActualCanonicalBoundary318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELActualPuncturedQuotientMap318 PELActualBoundarySixCorners318
open PELOriginalMaximalQuotient318

/-- An ambient extension of the SAME upper-half-plane projection. Its
arbitrary lower-half-plane value is never used for analytic claims. -/
@[expose] def ambientProjection (z:ℂ) : MaximalBase := by
  classical
  exact if h:0<z.im then maximalProjection ⟨z,h⟩ else cutProjection ⟨corner 0,corner_mem 0⟩

theorem ambientProjection_upper (τ:HalfPlane) :
    ambientProjection τ=maximalProjection τ := by
  simp only [ambientProjection,dif_pos τ.property]

theorem ambientProjection_continuousOn :
    ContinuousOn ambientProjection {z:ℂ|0<z.im} := by
  apply continuousOn_iff_continuous_restrict.mpr
  have he:(fun τ:HalfPlane=>ambientProjection τ)=maximalProjection :=
    funext ambientProjection_upper
  rw [he]
  exact maximalProjection_continuous

theorem ambientProjection_continuousAt {z:ℂ} (hz:0<z.im) :
    ContinuousAt ambientProjection z :=
  (ambientProjection_continuousOn z hz).continuousAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)

@[expose] def ambientMap (f:ℂ→ℂ) : ℂ→OnePoint ℂ := totalMap f ∘ ambientProjection

section Conformal
variable (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    (hmirror:∀z∈openDomain,f (J z)=J (f z))
include hf hfa hmirror

theorem ambientMap_continuousAt {z:ℂ} (hz:0<z.im)
    (hq:ambientProjection z∈regularBase) : ContinuousAt (ambientMap f) z :=
  (totalMap_continuousAt disk f hf hfa hmirror hq).comp
    (ambientProjection_continuousAt hz)

/-- Exact canonical formula for every genuine closed-cut representative
whose original arithmetic image is not an excluded corner image. -/
theorem ambientMap_closed {z:ℂ} (hz:z∈closedDomain)
    (hq:ambientProjection z∈regularBase) :
    ambientMap f z=ReflectedDiskJoukowski318.joukowski (trace f z) := by
  obtain ⟨P,rfl⟩:=hz
  have hp:cutProjection P∈regularBase := by
    simpa only [ambientProjection_upper] using hq
  let Q:regularCut:=⟨P,hp⟩
  change totalMap f (ambientProjection (cutPoint P))=_
  rw [ambientProjection_upper]
  exact totalMap_agrees disk f hf hfa hmirror Q

theorem ambientMap_interior {z:ℂ} (hz:z∈openDomain)
    (hq:ambientProjection z∈regularBase) :
    ambientMap f z=ReflectedDiskJoukowski318.joukowski (f z) := by
  rw [ambientMap_closed disk f hf hfa hmirror (openDomain_subset hz) hq,
    trace_on_interior disk f hf hfa hz]
end Conformal
end PELActualAmbientProjection318
