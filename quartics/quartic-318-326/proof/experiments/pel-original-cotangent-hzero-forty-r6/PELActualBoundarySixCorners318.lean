module
public import PELActualRegularEdgeExtension318
public section
noncomputable section
namespace PELActualBoundarySixCorners318
open Set Filter
open scoped Topology
open PELMaximalActualComplexDomain318 PELActualEdgeHalfNeighborhood318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
set_option maxHeartbeats 2800000

@[expose] def corner : Fin 6→ℝ×ℝ :=
  ![(-30,0),(-30,5/7),(-28,1),(28,1),(30,5/7),(30,0)]

theorem corner_mem (k:Fin 6) : corner k∈upperCut := by
  fin_cases k <;> norm_num [corner,upperCut]

@[expose] def complexCorner (k:Fin 6) : ℂ := (cutPoint ⟨corner k,corner_mem k⟩:ℂ)
@[expose] def corners : Set ℂ := Set.range complexCorner

theorem corners_finite : corners.Finite := Set.finite_range complexCorner

theorem closed_slacks {z:ℂ} (hz:z∈closedDomain) : ∀i:Fin 6,0≤slack i z := by
  obtain ⟨_,hP⟩ := (closedDomain_membership z).mp hz
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hP
  intro i
  fin_cases i <;> norm_num [slack] <;> linarith

/-- Two different active original constraints force one of the six
literal polygon corners. This is exhaustive exact affine arithmetic,
not a sample of boundary points or an assumed cellulation. -/
theorem double_active_corner {z:ℂ} (hz:z∈closedDomain)
    (i j:Fin 6) (hij:i≠j) (hi:slack i z=0) (hj:slack j z=0) :
    ∃k:Fin 6,coordinates z=corner k := by
  obtain ⟨_,hP⟩ := (closedDomain_membership z).mp hz
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hP
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨5,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · refine ⟨0,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · exact False.elim (hij rfl)
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨3,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · refine ⟨2,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · refine ⟨5,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · exact False.elim (hij rfl)
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨4,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨0,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · exact False.elim (hij rfl)
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨1,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨3,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · refine ⟨4,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · exact False.elim (hij rfl)
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨2,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · refine ⟨1,?_⟩
    norm_num [slack] at hi hj
    apply Prod.ext <;> norm_num [corner] <;> linarith
  · norm_num [slack] at hi hj
    exfalso
    linarith
  · exact False.elim (hij rfl)

theorem coordinates_corner_recovers {z:ℂ} (hz:z∈closedDomain) {k:Fin 6}
    (hk:coordinates z=corner k) : z=complexCorner k := by
  obtain ⟨hi,hP⟩ := (closedDomain_membership z).mp hz
  have he : (⟨coordinates z,hP⟩:upperCut)=⟨corner k,corner_mem k⟩ := Subtype.ext hk
  have hh := cutPoint_recovers ⟨z,hi⟩ hP
  rw [he] at hh
  exact (congrArg (fun q:QuaternionicJointPeriodTopology318.HalfPlane=>(q:ℂ)) hh).symm

/-- Every point of the actual closed boundary is either a regular point
of one of the six actual edges, or one of the six explicit complex
corner points. No extra exceptional set is postulated. -/
theorem closed_boundary_regular_or_corner {z:ℂ}
    (hz:z∈closedDomain) (hnot:z∉openDomain) :
    (∃i:Fin 6,RegularEdge i z) ∨ z∈corners := by
  classical
  have him:=((closedDomain_membership z).mp hz).1
  have hnn:=closed_slacks hz
  have hn:¬∀i:Fin 6,0<slack i z := by
    intro h
    exact hnot ((original_domain_iff z).mpr ⟨him,h⟩)
  push_neg at hn
  obtain ⟨i,hi⟩ := hn
  have hi0:slack i z=0 := le_antisymm hi (hnn i)
  by_cases ho:∀j:Fin 6,j≠i → 0<slack j z
  · exact Or.inl ⟨i,him,hi0,ho⟩
  · push_neg at ho
    obtain ⟨j,hji,hj⟩ := ho
    have hj0:slack j z=0 := le_antisymm hj (hnn j)
    obtain ⟨k,hk⟩ := double_active_corner hz i j (Ne.symm hji) hi0 hj0
    exact Or.inr ⟨k,(coordinates_corner_recovers hz hk).symm⟩

/-- This also covers the ambient complex frontier, since the actual
closed-domain image is compact and contains the whole open domain. -/
theorem frontier_regular_or_corner {z:ℂ} (hz:z∈frontier openDomain) :
    (∃i:Fin 6,RegularEdge i z) ∨ z∈corners := by
  apply closed_boundary_regular_or_corner
  · exact closure_minimal openDomain_subset closedDomain_compact.isClosed hz.1
  · simpa only [openDomain_open.interior_eq] using hz.2
/-- The analytic edge extension covers the ENTIRE actual frontier
except this explicitly constructed finite set of six cut corners.
These geometric corners are not being identified with arithmetic branch
values, which are a different quotient-level object. -/
theorem actual_frontier_extension_except_corners
    (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    {z:ℂ} (hz:z∈frontier openDomain) (hn:z∉corners) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ F=ᶠ[𝓝[openDomain] z] f ∧ ‖F z‖=1 := by
  rcases frontier_regular_or_corner hz with ⟨i,hi⟩|hc
  · exact PELActualRegularEdgeExtension318.actual_regular_edge_extension disk f hf hfa hi
  · exact False.elim (hn hc)
end PELActualBoundarySixCorners318
