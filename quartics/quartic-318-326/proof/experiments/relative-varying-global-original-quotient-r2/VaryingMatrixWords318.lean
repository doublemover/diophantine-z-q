module
public import VaryingCommutingMatrixPoints318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public section
noncomputable section
namespace VaryingMatrixWords318
open VaryingCommutingMatrixRing318 VaryingCommutingMatrixPoints318
universe u
variable {σ ι S : Type u} [CommRing S] [Fintype ι]

/-- Literal successive matrix actions on the marked vector. All finite
words, including the empty word, are retained as possible basis columns. -/
@[expose] def wordVector (d : Data σ ι S) : List σ → (ι → S)
  | [] => d.marked
  | s::l => d.matrices s *ᵥ wordVector d l

@[expose] def columns (d : Data σ ι S) (w : ι → List σ) : Matrix ι ι S :=
  fun i j => wordVector d (w j) i

variable [DecidableEq ι]
@[expose] def determinant (d : Data σ ι S) (w : ι → List σ) : S := (columns d w).det

variable (R : Type u) [CommRing R] [Algebra R S]
  {T : Type u} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)

lemma wordVector_map (d : Data σ ι S) (l : List σ) (i : ι) :
    f (wordVector d l i)=wordVector (mapData R σ ι S T f d) l i := by
  induction l generalizing i with
  | nil => rfl
  | cons s l ih =>
    simp only [wordVector,Matrix.mulVec_apply_eq_sum,map_sum,map_mul,mapData]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

lemma determinant_map (d : Data σ ι S) (w : ι → List σ) :
    f (determinant d w)=determinant (mapData R σ ι S T f d) w := by
  change f.toRingHom (columns d w).det = _
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  exact wordVector_map R f d (w j) i
end VaryingMatrixWords318
