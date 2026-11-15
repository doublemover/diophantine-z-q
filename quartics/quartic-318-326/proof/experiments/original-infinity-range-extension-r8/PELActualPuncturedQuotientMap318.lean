module
public import PELActualCanonicalBoundary318
public import OpenRestrictedQuotientDescent318
public section
noncomputable section
namespace PELActualPuncturedQuotientMap318
open Set Topology
open scoped OnePoint
open PELMaximalActualComplexDomain318 PELActualCanonicalBoundary318
open PELActualBoundarySixCorners318 PELActualDomainClosure318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonBoundary318
open PELOriginalMaximalSphere318 PELOriginalMaximalQuotient318
set_option maxHeartbeats 3000000

/-- Actual arithmetic images of the six geometric corners. Different
corners may have the same image; no cardinality or branch count is assumed. -/
@[expose] def cornerImages : Set MaximalBase :=
  Set.range (fun k:Fin 6=>cutProjection ⟨corner k,corner_mem k⟩)
@[expose] def regularBase : Set MaximalBase := cornerImagesᶜ
@[expose] def regularCut : Set upperCut := cutProjection ⁻¹' regularBase

theorem cornerImages_finite : cornerImages.Finite := Set.finite_range _
theorem regularBase_open : IsOpen regularBase := cornerImages_finite.isClosed.isOpen_compl

theorem cut_quotient : IsQuotientMap cutProjection :=
  cutProjection_continuous.isClosedMap.isQuotientMap
    cutProjection_continuous cutProjection_surjective

@[expose] def regularProjection : regularCut→regularBase :=
  regularBase.restrictPreimage cutProjection

theorem regularProjection_quotient : IsQuotientMap regularProjection :=
  cut_quotient.restrictPreimage_isOpen regularBase_open

theorem original_noncorner (P:regularCut) : (cutPoint P.val:ℂ)∈puncturedClosed := by
  refine ⟨⟨P.val,rfl⟩,?_⟩
  rintro ⟨k,hk⟩
  have hp:P.val=(⟨corner k,corner_mem k⟩:upperCut) := by
    apply Subtype.ext
    have h:=congrArg coordinates hk
    change coordinates (cutPoint ⟨corner k,corner_mem k⟩)=coordinates (cutPoint P.val) at h
    simpa only [coordinates_halfPlane,cutPoint_coordinates] using h.symm
  apply P.property
  exact ⟨k,congrArg cutProjection hp.symm⟩

@[expose] def cutTrace (f:ℂ→ℂ) (P:regularCut) : OnePoint ℂ :=
  ReflectedDiskJoukowski318.joukowski (trace f (cutPoint P.val))


/-- The actual punctured arithmetic map, not a redefined quotient or a
map transported through the old topological sphere. -/
@[expose] def puncturedMap (f:ℂ→ℂ) : regularBase→OnePoint ℂ :=
  OpenRestrictedQuotientDescent318.descended regularProjection
    regularProjection_quotient.surjective (cutTrace f)



/-- Total ambient map with arbitrary infinity values ONLY at the excluded
finite corner images. No continuity at those values is asserted here. -/
@[expose] def totalMap (f:ℂ→ℂ) (q:MaximalBase) : OnePoint ℂ := by
  classical
  exact if h:q∈regularBase then puncturedMap f ⟨q,h⟩ else ∞

theorem totalMap_eq (f:ℂ→ℂ) (q:regularBase) : totalMap f q=puncturedMap f q := by
  simp only [totalMap,dif_pos q.property]

section Conformal
variable (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    (hmirror:∀z∈openDomain,f (J z)=J (f z))
include hf hfa

theorem cutTrace_continuous : Continuous (cutTrace f) := by
  let lift:regularCut→puncturedClosed := fun P=>⟨(cutPoint P.val:ℂ),original_noncorner P⟩
  have hl:Continuous lift :=
    (continuous_subtype_val.comp (cutPoint_continuous.comp continuous_subtype_val)).subtype_mk _
  have ht:Continuous (fun z:puncturedClosed=>trace f z) :=
    (continuousOn_iff_continuous_restrict.mp (trace_continuous disk f hf hfa))
  exact ReflectedDiskJoukowskiTopology318.joukowski_continuous.comp (ht.comp hl)

include hmirror
/-- Exact original arithmetic fibers are respected by the canonical
trace, using independently proved boundary reflection and unit values. -/
theorem cutTrace_fibers (P Q:regularCut)
    (h:regularProjection P=regularProjection Q) : cutTrace f P=cutTrace f Q := by
  have he:cutProjection P.val=cutProjection Q.val := congrArg Subtype.val h
  rcases (cutProjection_fibers P.val Q.val).mp he with hp|⟨hb,hq⟩
  · have he':P=Q:=Subtype.ext hp
    rw [he']
  · have hn:(cutPoint P.val:ℂ)∉openDomain := by
      intro ho
      have hc:coordinates (cutPoint P.val)=P.val.val := by
        rw [coordinates_halfPlane,cutPoint_coordinates]
      have hi:(upperCutCenter P.val).val∈strictPolygon := by
        simpa only [hc] using ho.2
      have hnot:(upperCutCenter P.val).val∉strictPolygon := by
        simpa only [interior_eq_strict] using hb.2
      exact hnot hi
    have hpoint:(cutPoint Q.val:ℂ)=J (cutPoint P.val) := by
      rw [hq,cutPoint_reflection]
      rfl
    change ReflectedDiskJoukowski318.joukowski (trace f (cutPoint P.val))=
      ReflectedDiskJoukowski318.joukowski (trace f (cutPoint Q.val))
    rw [hpoint]
    exact (boundary_sphere_trace_mirror disk f hf hfa hmirror (original_noncorner P) hn).symm


theorem puncturedMap_agrees (P:regularCut) :
    puncturedMap f (regularProjection P)=cutTrace f P :=
  OpenRestrictedQuotientDescent318.descended_agrees regularProjection
    regularProjection_quotient.surjective (cutTrace f)
    (cutTrace_fibers disk f hf hfa hmirror) P

theorem puncturedMap_continuous : Continuous (puncturedMap f) :=
  OpenRestrictedQuotientDescent318.descended_continuous regularProjection
    regularProjection_quotient (cutTrace f) (cutTrace_continuous disk f hf hfa)
    (cutTrace_fibers disk f hf hfa hmirror)


theorem totalMap_continuousOn : ContinuousOn (totalMap f) regularBase := by
  apply continuousOn_iff_continuous_restrict.mpr
  have he:(fun q:regularBase=>totalMap f q)=puncturedMap f :=
    funext (totalMap_eq f)
  rw [he]
  exact puncturedMap_continuous disk f hf hfa hmirror

theorem totalMap_continuousAt {q:MaximalBase} (hq:q∈regularBase) :
    ContinuousAt (totalMap f) q :=
  (totalMap_continuousOn disk f hf hfa hmirror q hq).continuousAt
    (regularBase_open.mem_nhds hq)

theorem totalMap_agrees (P:regularCut) :
    totalMap f (cutProjection P.val)=cutTrace f P := by
  change totalMap f (regularProjection P).val=_
  rw [totalMap_eq f (regularProjection P)]
  exact puncturedMap_agrees disk f hf hfa hmirror P

/-- At every original interior representative, the descended value is
the genuine interior Joukowski map, with exact equality rather than a
homotopy or source-transported complex structure. -/
theorem puncturedMap_interior (P:regularCut) (hP:(cutPoint P.val:ℂ)∈openDomain) :
    puncturedMap f (regularProjection P)=
      ReflectedDiskJoukowski318.joukowski (f (cutPoint P.val)) := by
  rw [puncturedMap_agrees disk f hf hfa hmirror]
  change ReflectedDiskJoukowski318.joukowski (trace f (cutPoint P.val))=_
  rw [trace_on_interior disk f hf hfa hP]
end Conformal
end PELActualPuncturedQuotientMap318
