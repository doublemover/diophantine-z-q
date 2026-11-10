module
public import PELOriginalPolygonBoundary318
public section
noncomputable section
namespace PELOriginalOpenEdgeDisjoint318
open PELDirichletSidePairingData318 PELDirichletIncidence318
open PELOriginalProjectiveTangents318 PELOriginalPolygonBoundary318 PELRealKleinSideTransport318
set_option maxHeartbeats 1800000

/-- The only original row vanishing at both endpoints of an original edge
is that edge's own row. This is the full28-by28 incidence test. -/
theorem both_endpoints_iff : ∀ (e f : Fin 28),
    (sideValue f (vertex (start e))=0 ∧ sideValue f (vertex (finish e))=0) ↔ f=e := by decide

theorem realSideValue_vertex (f v : Fin 28) :
    realSideValue f (realPoint (vertex v))=(sideValue f (vertex v):ℝ) := by
  simp [realSideValue,sideValue,realPoint]

theorem realSideValue_mix (f : Fin 28) (P Q : ℝ×ℝ) (s : ℝ) :
    realSideValue f (realMix P Q s)=(1-s)*realSideValue f P+s*realSideValue f Q := by
  simp only [realSideValue,realMix]
  ring

/-- On an entire OPEN real original side precisely one of the28 distinct
rows is active. Both endpoints are excluded by the actual strict parameter. -/
theorem open_side_active_iff (e f : Fin 28) (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    realSideValue f (realMix (realPoint (vertex (start e)))
      (realPoint (vertex (finish e))) s)=0 ↔ f=e := by
  have hA : 0≤realSideValue f (realPoint (vertex (start e))) := by
    rw [realSideValue_vertex]
    exact_mod_cast vertex_all_rows (start e) f
  have hB : 0≤realSideValue f (realPoint (vertex (finish e))) := by
    rw [realSideValue_vertex]
    exact_mod_cast vertex_all_rows (finish e) f
  rw [realSideValue_mix]
  constructor
  · intro h
    have hzA : realSideValue f (realPoint (vertex (start e)))=0 := by nlinarith
    have hzB : realSideValue f (realPoint (vertex (finish e)))=0 := by nlinarith
    rw [realSideValue_vertex] at hzA hzB
    exact (both_endpoints_iff e f).mp ⟨by exact_mod_cast hzA,by exact_mod_cast hzB⟩
  · rintro rfl
    rw [realSideValue_vertex,realSideValue_vertex,(boundary_endpoints e).1,(boundary_endpoints e).2]
    norm_num

/-- Distinct original open sides are genuinely disjoint subsets of the
real polygon, not merely distinct finite names. -/
theorem open_sides_disjoint (e f : Fin 28) (s t : ℝ)
    (hs : 0<s) (hs1 : s<1) (ht : 0<t) (ht1 : t<1)
    (h : realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s=
      realMix (realPoint (vertex (start f))) (realPoint (vertex (finish f))) t) : e=f := by
  have hf := (open_side_active_iff f f t ht ht1).mpr rfl
  rw [← h] at hf
  exact ((open_side_active_iff e f s hs hs1).mp hf).symm
/-- Every literal vertex has another active side distinct from any given
one. This finite certificate retains all original vertex exceptional cases. -/
theorem another_active_side : ∀ (v e : Fin 28),
    ∃ f : Fin 28, f≠e ∧ sideValue f (vertex v)=0 := by decide

theorem open_side_not_vertex (e v : Fin 28) (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s≠
      realPoint (vertex v) := by
  intro h
  obtain ⟨f,hfe,hf⟩ := another_active_side v e
  have hz : realSideValue f (realPoint (vertex v))=0 := by
    rw [realSideValue_vertex,hf]
    norm_num
  rw [← h] at hz
  exact hfe ((open_side_active_iff e f s hs hs1).mp hz)

/-- The literal real edge parameter recovers every affine parameter exactly. -/
theorem edgeParameter_mix (e : Fin 28) (s : ℝ) :
    edgeParameter e (realMix (realPoint (vertex (start e)))
      (realPoint (vertex (finish e))) s)=s := by
  fin_cases e <;> norm_num [edgeParameter,realMix,realPoint,vertex,start,finish] <;> ring
end PELOriginalOpenEdgeDisjoint318
