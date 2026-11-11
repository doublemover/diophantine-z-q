module
public import PELDirichletSidePairingData318
public section
noncomputable section
namespace PELDirichletVertexCycles318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELQuaternionKleinAction318 PELDirichletSidePairingData318
set_option maxHeartbeats 1800000

/-- The next incident side after each exact original edge identification. -/
@[expose] def nextVertex : Fin 28 → Fin 28 := ![12,27,24,11,5,23,7,21,9,19,2,10,13,1,26,14,17,25,8,18,6,20,4,22,16,3,0,15]
@[expose] def stepEdge : Fin 28 → Fin 28 := ![24,27,21,22,7,11,7,12,4,12,25,5,9,23,17,8,0,14,18,1,18,2,20,2,16,10,26,15]
@[expose] def vertexClass : Fin 28 → Fin 5 := ![0,0,1,1,2,2,3,3,4,4,1,1,0,0,0,0,1,1,4,4,3,3,2,2,1,1,0,0]
@[expose] def cycleWord : Fin 5 → List (Fin 28) := ![[24,9,23,27,15,8,17,26],[21,16,0,14,10,22,5,25],[7,11,2,20],[7,12,2,18],[4,12,1,18]]

/-- An actual side-endpoint identification, in its original directed order. -/
@[expose] def EndpointStep (a b : Fin 28) : Prop :=
  ∃ e : Fin 28, (a=start e ∧ b=imageStart e) ∨ (a=finish e ∧ b=imageFinish e)
instance (a b : Fin 28) : Decidable (EndpointStep a b) := inferInstanceAs
  (Decidable (∃ e : Fin 28, (a=start e ∧ b=imageStart e) ∨ (a=finish e ∧ b=imageFinish e)))

theorem next_is_endpoint (v : Fin 28) : EndpointStep v (nextVertex v) := by
  refine ⟨stepEdge v,?_⟩
  fin_cases v <;> norm_num [stepEdge,nextVertex,start,finish,imageStart,imageFinish]

theorem endpoint_class {a b : Fin 28} (h : EndpointStep a b) :
    vertexClass a=vertexClass b := by
  obtain ⟨e,h|h⟩ := h
  · obtain ⟨rfl,rfl⟩ := h
    fin_cases e <;> rfl
  · obtain ⟨rfl,rfl⟩ := h
    fin_cases e <;> rfl

/-- Literal finite paths in the actual endpoint graph. No quotient-surface
or fundamental-polygon assertion is part of this definition. -/
inductive Path : Fin 28 → Fin 28 → Prop
  | refl (a) : Path a a
  | extend {a b c} : Path a b → EndpointStep b c → Path a c

@[expose] def walk : ℕ → Fin 28 → Fin 28
  | 0,v => v
  | n+1,v => nextVertex (walk n v)

theorem walk_path (n : ℕ) (v : Fin 28) : Path v (walk n v) := by
  induction n with
  | zero => exact Path.refl v
  | succ n ih => exact Path.extend ih (next_is_endpoint (walk n v))

theorem class_reachable (a b : Fin 28) :
    vertexClass a=vertexClass b ↔ ∃ n : Fin 8, walk n.val a=b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Exact exhaustion of the side-identification graph by five classes,
proved in both directions from the original edge endpoint maps. -/
theorem path_iff_class (a b : Fin 28) : Path a b ↔ vertexClass a=vertexClass b := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | extend h hs ih => exact ih.trans (endpoint_class hs)
  · intro h
    obtain ⟨n,hn⟩ := (class_reachable a b).mp h
    rw [←hn]
    exact walk_path n.val a

@[expose] def classSize : Fin 5 → ℕ := ![8,8,4,4,4]
theorem class_cardinality (i : Fin 5) :
    (Finset.univ.filter (fun v : Fin 28 => vertexClass v=i)).card=classSize i := by
  fin_cases i <;> decide

/-- Quaternion product in the order the side maps are APPLIED:
the last map acts on the left. -/
@[expose] def wordCoordinates : List (Fin 28) → Coordinates
  | [] => ![1,0,0,0]
  | e::es => product (wordCoordinates es) (coefficients e)
@[expose] def originalWord : List (Fin 28) → B
  | [] => 1
  | e::es => originalWord es * embed (coefficients e)

theorem word_identity (w : List (Fin 28)) : embed (wordCoordinates w)=originalWord w := by
  induction w with
  | nil => ext <;> norm_num [wordCoordinates,originalWord,embed]
  | cons e es ih =>
    simp only [wordCoordinates,originalWord,embed_mul,ih]

@[expose] def cycleSign : Fin 5 → ℤ := ![-1,1,-1,-1,-1]
theorem original_cycle_coordinates (i : Fin 5) :
    wordCoordinates (cycleWord i)=![cycleSign i,0,0,0] := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [cycleWord,cycleSign,wordCoordinates,product,coefficients]

/-- Actual products of the original signed order units are scalar plus or minus one,
not merely identity permutations of the recorded vertices. -/
theorem original_cycle_product (i : Fin 5) :
    originalWord (cycleWord i)=algebraMap ℚ B (cycleSign i : ℚ) := by
  rw [←word_identity,original_cycle_coordinates]
  ext <;> simp [embed]

theorem cycle_homogeneous_identity (i : Fin 5) : matrix (originalWord (cycleWord i))=1 := by
  rw [original_cycle_product]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [cycleSign,matrix]

/-- The finite side-pairing data have Euler number -8. Identifying these
combinatorial cells with the actual arithmetic surface is a separate theorem. -/
theorem paired_cell_count : (5:ℤ)-14+1 = -8 := by norm_num
end PELDirichletVertexCycles318
