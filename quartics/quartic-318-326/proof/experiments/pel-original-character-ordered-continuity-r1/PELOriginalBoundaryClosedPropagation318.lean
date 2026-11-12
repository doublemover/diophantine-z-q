module
public import PELActualBoundarySixCorners318
public import PELOriginalConformalComparisonInputs318
public section
noncomputable section
namespace PELOriginalBoundaryClosedPropagation318
open Set
open scoped OnePoint
open PELMaximalActualComplexDomain318 PELActualEdgeHalfNeighborhood318
open PELActualBoundarySixCorners318 PELMaximalHalfOctagonCoordinates318
open PELMaximalHalfOctagonOriginalPoints318 PELMaximalHalfOctagonShape318
open PELOriginalMaximalQuotient318 ComplexSphereRegularTarget318
set_option maxHeartbeats 2400000

@[expose] def nextCorner : Fin 6→Fin 6 := ![1,2,3,4,5,0]
@[expose] def outgoingEdge : Fin 6→Fin 6 := ![3,5,1,4,2,0]
@[expose] def cornerSegment (k:Fin 6) (t:ℝ) : ℝ×ℝ :=
  ((1-t)*(corner k).1+t*(corner (nextCorner k)).1,
    (1-t)*(corner k).2+t*(corner (nextCorner k)).2)

theorem cornerSegment_continuous (k:Fin 6) : Continuous (cornerSegment k) := by
  unfold cornerSegment
  fun_prop

theorem cornerSegment_zero (k:Fin 6) : cornerSegment k 0=corner k := by
  simp [cornerSegment]

theorem cornerSegment_mem (k:Fin 6) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
    cornerSegment k t∈upperCut := by
  obtain ⟨ht0,ht1⟩:=ht
  fin_cases k <;> norm_num [cornerSegment,corner,nextCorner,upperCut] <;>
    repeat' constructor <;> linarith

/-- Each literal corner is approached along its outgoing genuine edge.
All OTHER five constraints are strict for every parameter in (0,1). -/
theorem cornerSegment_regular (k:Fin 6) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    RegularEdge (outgoingEdge k)
      (cutPoint ⟨cornerSegment k t,cornerSegment_mem k ⟨ht.1.le,ht.2.le⟩⟩:ℂ) := by
  let P:upperCut:=⟨cornerSegment k t,cornerSegment_mem k ⟨ht.1.le,ht.2.le⟩⟩
  have hcoords:coordinates (cutPoint P)=cornerSegment k t := by
    rw [coordinates_halfPlane,cutPoint_coordinates]
  refine ⟨(cutPoint P).property,?_,?_⟩
  · change slack (outgoingEdge k) (cutPoint P)=0
    simp only [slack,hcoords]
    fin_cases k <;> norm_num [outgoingEdge,cornerSegment,corner,nextCorner] <;> ring
  · intro j hj
    change 0<slack j (cutPoint P)
    simp only [slack,hcoords]
    have ht0:=ht.1
    have ht1:=ht.2
    fin_cases k <;> fin_cases j <;>
      norm_num [outgoingEdge,cornerSegment,corner,nextCorner] at hj ⊢ <;> linarith

/-- Any closed subset of the actual cut containing every regular edge
point contains each of the SIX literal corners. The conclusion follows
from actual segment limits, not from assigning guessed vertex values. -/
theorem corner_mem_of_regular (S:Set upperCut) (hS:IsClosed S)
    (hreg:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) → P∈S)
    (k:Fin 6) : (⟨corner k,corner_mem k⟩:upperCut)∈S := by
  let T:Set (ℝ×ℝ):=Subtype.val '' S
  have hT:IsClosed T := (hS.isCompact.image continuous_subtype_val).isClosed
  have hsub:Ioo (0:ℝ) 1⊆cornerSegment k ⁻¹' T := by
    intro t ht
    refine ⟨⟨cornerSegment k t,cornerSegment_mem k ⟨ht.1.le,ht.2.le⟩⟩,
      hreg _ (outgoingEdge k) (cornerSegment_regular k ht),rfl⟩
  have hclosed:IsClosed (cornerSegment k ⁻¹' T) :=
    hT.preimage (cornerSegment_continuous k)
  have hz:(0:ℝ)∈closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
    norm_num
  have hm:corner k∈T := by
    simpa only [Set.mem_preimage,cornerSegment_zero] using closure_minimal hsub hclosed hz
  obtain ⟨Q,hQ,hQe⟩:=hm
  have he:Q=(⟨corner k,corner_mem k⟩:upperCut):=Subtype.ext hQe
  exact he ▸ hQ

/-- Exhaustive regular-or-six-corner classification upgrades regular-edge
membership in a closed set to membership of the ENTIRE cut boundary. -/
theorem whole_boundary_mem (S:Set upperCut) (hS:IsClosed S)
    (hreg:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) → P∈S)
    (P:upperCut) (hP:(upperCutCenter P).val∉strictPolygon) : P∈S := by
  have hz:(cutPoint P:ℂ)∈closedDomain:=⟨P,rfl⟩
  have hn:(cutPoint P:ℂ)∉openDomain := by
    intro ho
    apply hP
    have hc:coordinates (cutPoint P)=P.val := by
      rw [coordinates_halfPlane,cutPoint_coordinates]
    simpa only [hc] using ho.2
  rcases closed_boundary_regular_or_corner hz hn with ⟨i,hi⟩|⟨k,hk⟩
  · exact hreg P i hi
  · have he:P=(⟨corner k,corner_mem k⟩:upperCut) := by
      apply Subtype.ext
      have hc:=congrArg coordinates hk
      change coordinates (cutPoint ⟨corner k,corner_mem k⟩)=coordinates (cutPoint P) at hc
      simpa only [coordinates_halfPlane,cutPoint_coordinates] using hc.symm
    rw [he]
    exact corner_mem_of_regular S hS hreg k

/-- The noncorner original edge points are dense along the whole actual
cut boundary, as a statement in the genuine cut topology. -/
theorem boundary_in_closure_regular (P:upperCut)
    (hP:(upperCutCenter P).val∉strictPolygon) :
    P∈closure {Q:upperCut | ∃i:Fin 6,RegularEdge i (cutPoint Q:ℂ)} := by
  apply whole_boundary_mem _ isClosed_closure _ P hP
  intro Q i hi
  exact subset_closure ⟨i,hi⟩

theorem regular_open : IsOpen regular :=
  OnePoint.isOpenMap_coe _ (isOpen_ne Complex.continuous_re continuous_const)

/-- Continuity of the ACTUAL filled map propagates the regular-edge
image exclusion through the six corners. This produces exactly the
all-boundary premise needed by the global original comparison. -/
theorem original_boundary_exclusion (F:MaximalBase→OnePoint ℂ) (hF:Continuous F)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      F (cutProjection P)∉regular) :
    ∀P:upperCut,(upperCutCenter P).val∉strictPolygon → F (cutProjection P)∉regular := by
  let S:Set upperCut:=(F ∘ cutProjection) ⁻¹' regularᶜ
  have hS:IsClosed S := regular_open.isClosed_compl.preimage
    (hF.comp cutProjection_continuous)
  intro P hP
  exact whole_boundary_mem S hS hedge P hP

/-- A convenient consumer of the CONSTRUCTED unit edge traces. No corner
value, injectivity at a corner, or boundary homeomorphism is assumed. -/
theorem original_boundary_exclusion_of_unit_traces
    (F:MaximalBase→OnePoint ℂ) (hF:Continuous F)
    (hedge:∀P:upperCut,∀i:Fin 6,RegularEdge i (cutPoint P:ℂ) →
      ∃w:ℂ,‖w‖=1 ∧ F (cutProjection P)=ReflectedDiskJoukowski318.joukowski w) :
    ∀P:upperCut,(upperCutCenter P).val∉strictPolygon → F (cutProjection P)∉regular := by
  apply original_boundary_exclusion F hF
  intro P i hi
  obtain ⟨w,hw,he⟩:=hedge P i hi
  rw [he]
  exact unit_boundary_not_regular w hw
end PELOriginalBoundaryClosedPropagation318
