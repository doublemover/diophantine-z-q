module
public import VaryingWordDeterminantOpen318
public import Mathlib.Data.Matrix.Basic
public section
noncomputable section
namespace VaryingSourceActionEquations318
open VaryingCommutingMatrixRing318 VaryingCommutingMatrixPoints318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

/-- Every original source element is a coordinate index. This canonical
presentation is allowed to be infinite; no finite-presentation claim is made. -/
inductive Index where
  | zero (i j : ι)
  | one (i j : ι)
  | add (a b : A) (i j : ι)
  | mul (a b : A) (i j : ι)
  | scalar (r : R) (i j : ι)

variable (S : Type u) [CommRing S] [Algebra R S]
@[expose] def equation (d : Data A ι S) : Index R A ι → S
  | .zero i j => d.matrices 0 i j
  | .one i j => d.matrices 1 i j - (1 : Matrix ι ι S) i j
  | .add a b i j => d.matrices (a+b) i j - (d.matrices a+d.matrices b) i j
  | .mul a b i j => d.matrices (a*b) i j - (d.matrices a*d.matrices b) i j
  | .scalar r i j => d.matrices (algebraMap R A r) i j -
      (algebraMap R (Matrix ι ι S) r) i j

abbrev Valid (d : Data A ι S) := ∀ t : Index R A ι, equation R A ι S d t=0

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma equation_map (d : Data A ι S) (t : Index R A ι) :
    f (equation R A ι S d t)=
      equation R A ι T (mapData R A ι S T f d) t := by
  cases t with
  | zero i j => rfl
  | one i j =>
    simp only [equation,mapData,map_sub,Matrix.one_apply]
    split_ifs <;> simp
  | add a b i j =>
    change f (d.matrices (a+b) i j-(d.matrices a i j+d.matrices b i j))=
      f (d.matrices (a+b) i j)-(f (d.matrices a i j)+f (d.matrices b i j))
    rw [map_sub,map_add]
  | mul a b i j =>
    change f (d.matrices (a*b) i j-∑ k,d.matrices a i k*d.matrices b k j)=
      f (d.matrices (a*b) i j)-∑ k,f (d.matrices a i k)*f (d.matrices b k j)
    simp only [map_sub,map_sum,map_mul]
  | scalar r i j =>
    simp only [equation,mapData,map_sub,Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

lemma valid_map (d : Data A ι S) (h : Valid R A ι S d) :
    Valid R A ι T (mapData R A ι S T f d) := by
  intro t
  rw [← equation_map,h,map_zero]
end VaryingSourceActionEquations318
