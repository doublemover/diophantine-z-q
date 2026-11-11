module
public import PELOriginalCWCharacteristicMaps318
public import Mathlib.Topology.CWComplex.Classical.Finite
public section
noncomputable section
namespace PELOriginalFiniteCW318
open Set Metric Topology
open PELUnlevelledComplexBase318 PELOriginalCWCharacteristicMaps318
open PELOriginalVertexStratum318 PELOriginalEdgeStrata318
open PELOriginalDiskAttachingStrata318
set_option maxHeartbeats 1800000

/-- These are cell indices for the actual arithmetic curve, not a separate
finite graph. Their characteristic maps below are its original projection. -/
@[expose] def Cell : ℕ → Type
  | 0 => Fin 5
  | 1 => Fin 14
  | 2 => Unit
  | _+3 => Empty

@[expose] def cellMap : (n : ℕ) → Cell n → PartialEquiv (Fin n → ℝ) UnlevelledBase
  | 0,i => vertexMap i
  | 1,i => edgeMap i
  | 2,_ => faceMap
  | _+3,i => nomatch i

theorem finite_cell : ∀ n, Finite (Cell n)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | _+3 => inferInstance

theorem source_eq : ∀ n (i : Cell n), (cellMap n i).source=ball 0 1
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | _+3,i => nomatch i

theorem continuous_cell : ∀ n (i : Cell n), ContinuousOn (cellMap n i) (closedBall 0 1)
  | 0,i => vertex_continuous i
  | 1,i => edge_continuous i
  | 2,_ => face_continuous
  | _+3,i => nomatch i

theorem continuous_inverse : ∀ n (i : Cell n),
    ContinuousOn (cellMap n i).symm (cellMap n i).target
  | 0,_ => CharacteristicPartialEquiv318.continuousOn_inverse ..
  | 1,_ => CharacteristicPartialEquiv318.continuousOn_inverse ..
  | 2,_ => CharacteristicPartialEquiv318.continuousOn_inverse ..
  | _+3,i => nomatch i

/-- Complete separation of all actual open cells, including across different
cell dimensions. In particular no boundary representative lies in the open disk. -/
theorem intersect_labels : ∀ n (i : Cell n) m (j : Cell m) (q : UnlevelledBase),
    q∈cellMap n i '' ball 0 1 → q∈cellMap m j '' ball 0 1 →
      (⟨n,i⟩ : Σ k, Cell k)=⟨m,j⟩
  | 0,i,0,j,q,hi,hj => by
      rw [show cellMap 0 i=vertexMap i from rfl,vertex_open] at hi
      rw [show cellMap 0 j=vertexMap j from rfl,vertex_open] at hj
      have hij := vertex_injective (hi.symm.trans hj)
      exact congrArg (fun k => (⟨0,k⟩ : Σ n,Cell n)) hij
  | 0,i,1,j,q,hi,hj => by
      change q∈vertexMap i '' ball 0 1 at hi
      change q∈edgeMap j '' ball 0 1 at hj
      rw [vertex_open] at hi
      rw [edge_open] at hj
      have hv : q∈VertexImage := by rw [hi]; exact (vertexEnumeration i).property
      exact False.elim (Set.disjoint_left.mp (edge_vertex_disjoint (edgeRepresentative j)) hj hv)
  | 0,i,2,j,q,hi,hj => by
      change q∈vertexMap i '' ball 0 1 at hi
      change q∈faceMap '' ball 0 1 at hj
      rw [vertex_open] at hi
      rw [face_open] at hj
      exact False.elim (Set.disjoint_left.mp (face_vertex_disjoint i) hj hi)
  | 1,i,0,j,q,hi,hj => by
      change q∈edgeMap i '' ball 0 1 at hi
      change q∈vertexMap j '' ball 0 1 at hj
      rw [edge_open] at hi
      rw [vertex_open] at hj
      have hv : q∈VertexImage := by rw [hj]; exact (vertexEnumeration j).property
      exact False.elim (Set.disjoint_left.mp (edge_vertex_disjoint (edgeRepresentative i)) hi hv)
  | 1,i,1,j,q,hi,hj => by
      change q∈edgeMap i '' ball 0 1 at hi
      change q∈edgeMap j '' ball 0 1 at hj
      rw [edge_open] at hi hj
      by_cases h : i=j
      · subst j; rfl
      · exact False.elim (Set.disjoint_left.mp (distinct_edge_strata_disjoint i j h) hi hj)
  | 1,i,2,j,q,hi,hj => by
      change q∈edgeMap i '' ball 0 1 at hi
      change q∈faceMap '' ball 0 1 at hj
      rw [edge_open] at hi
      rw [face_open] at hj
      exact False.elim (Set.disjoint_left.mp (face_edge_disjoint i) hj hi)
  | 2,i,0,j,q,hi,hj => by
      change q∈faceMap '' ball 0 1 at hi
      change q∈vertexMap j '' ball 0 1 at hj
      rw [face_open] at hi
      rw [vertex_open] at hj
      exact False.elim (Set.disjoint_left.mp (face_vertex_disjoint j) hi hj)
  | 2,i,1,j,q,hi,hj => by
      change q∈faceMap '' ball 0 1 at hi
      change q∈edgeMap j '' ball 0 1 at hj
      rw [face_open] at hi
      rw [edge_open] at hj
      exact False.elim (Set.disjoint_left.mp (face_edge_disjoint j) hi hj)
  | 2,i,2,j,_,_,_ => by cases i; cases j; rfl
  | _+3,i,_,_,_,_,_ => nomatch i
  | _,_,_+3,j,_,_,_ => nomatch j

theorem cells_disjoint : (Set.univ : Set (Σ n,Cell n)).PairwiseDisjoint
    (fun ni => cellMap ni.1 ni.2 '' ball 0 1) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro q ha hb
  exact hab (intersect_labels a.1 a.2 b.1 b.2 q ha hb)

/-- The actual attaching maps land in lower-dimensional actual closed cells.
The two-dimensional case uses the proved complete attaching-circle identity. -/
theorem boundary_lower : ∀ n (i : Cell n),
    MapsTo (cellMap n i) (sphere 0 1)
      (⋃ (m<n) (j : Cell m), cellMap m j '' closedBall 0 1)
  | 0,i => by
      intro z hz
      exact False.elim (vertex_boundary i z hz)
  | 1,i => by
      intro z hz
      obtain ⟨j,hj⟩ := vertex_cover _ (edge_boundary i z hz)
      exact Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨by omega,Set.mem_iUnion.mpr ⟨j,hj⟩⟩⟩
  | 2,_ => by
      intro z hz
      have h := face_boundary z hz
      rw [attaching_exact_lower_strata] at h
      rcases h with hv | he
      · obtain ⟨j,hj⟩ := vertex_cover _ hv
        exact Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨by omega,Set.mem_iUnion.mpr ⟨j,hj⟩⟩⟩
      · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
        obtain ⟨j,hj⟩ := edge_cover e _ he
        exact Set.mem_iUnion.mpr ⟨1,Set.mem_iUnion.mpr ⟨by omega,Set.mem_iUnion.mpr ⟨j,hj⟩⟩⟩
  | _+3,i => nomatch i

/-- The closed2-cell is already the entire original arithmetic curve. This
also supplies weak topology directly, without assuming a cell decomposition. -/
theorem whole_union : (⋃ (n : ℕ) (j : Cell n), cellMap n j '' closedBall 0 1)=Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : q∈faceMap '' closedBall 0 1 := by rw [face_closed]; trivial
  exact Set.mem_iUnion.mpr ⟨2,Set.mem_iUnion.mpr ⟨(),hq⟩⟩

theorem weak_topology (A : Set UnlevelledBase) (_ : A⊆Set.univ)
    (h : ∀ n (j : Cell n), IsClosed (A∩cellMap n j '' closedBall 0 1)) : IsClosed A := by
  have h2 := h 2 ()
  change IsClosed (A∩faceMap '' closedBall 0 1) at h2
  simpa only [face_closed,Set.inter_univ] using h2

/-- A genuine classical CW structure on the SAME original norm-one
arithmetic curve: five vertices, fourteen edges, and one2-cell. All maps,
attachment, separation and weak topology have been constructed above. -/
@[expose] def originalCW : CWComplex (Set.univ : Set UnlevelledBase) :=
  CWComplex.mkFiniteType Set.univ Cell cellMap finite_cell source_eq continuous_cell
    continuous_inverse cells_disjoint boundary_lower weak_topology whole_union

theorem no_higher_cells : ∀ n, 3≤n → IsEmpty (Cell n)
  | 0,h => by omega
  | 1,h => by omega
  | 2,h => by omega
  | _+3,_ => inferInstance

theorem original_finite : letI := originalCW; CWComplex.Finite (Set.univ : Set UnlevelledBase) := by
  letI := originalCW
  refine { eventually_isEmpty_cell := ?_, finite_cell := finite_cell }
  apply Filter.eventually_atTop.mpr
  exact ⟨3,fun n hn => no_higher_cells n hn⟩

theorem original_cell_counts :
    Nat.card (Cell 0)=5 ∧ Nat.card (Cell 1)=14 ∧ Nat.card (Cell 2)=1 := by
  simp [Cell]

/-- Alternating cell count of the constructed arithmetic CW structure.
Identifying this with an analytic/algebraic genus invariant is a later
comparison, not a hypothesis silently used in the construction. -/
theorem original_cell_sum : (Nat.card (Cell 0):ℤ)-(Nat.card (Cell 1):ℤ)+
    (Nat.card (Cell 2):ℤ) = -8 := by
  norm_num [Cell]
end PELOriginalFiniteCW318
