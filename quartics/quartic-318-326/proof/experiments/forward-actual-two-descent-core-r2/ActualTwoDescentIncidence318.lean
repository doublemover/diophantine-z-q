module
public import ActualOriginalFiniteMajorArcError318
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public section
noncomputable section
namespace ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Original support has d+1 members. None is its distinguished last
member; the d auxiliary columns are exactly e_i+e_last. This also retains
the one-support case d0, with no fictitious auxiliary prime. -/
@[expose] def incidence (d : ℕ) : Matrix (Option (Fin d)) (Fin d) (ZMod 2) :=
  fun i j => match i with
  | none => 1
  | some k => if k=j then 1 else 0

lemma actual_two_add (z : ZMod 2) : z+z=0 := by
  calc z+z = (2 : ZMod 2)*z := (two_mul z).symm
       _ = 0 := by norm_num

/-- Every column is even-sum, with no graph/rank assumption. -/
lemma actual_incidence_total (d : ℕ) (y : Fin d → ZMod 2) :
    (∑ i : Option (Fin d), (incidence d *ᵥ y) i)=0 := by
  simp only [Fintype.sum_option]
  have hnone : (incidence d *ᵥ y) none = ∑ j, y j := by
    simp [incidence,Matrix.mulVec,dotProduct]
  have hsome (i : Fin d) : (incidence d *ᵥ y) (some i)=y i := by
    simp [incidence,Matrix.mulVec,dotProduct]
  simp only [hnone,hsome]
  exact actual_two_add _

lemma actual_incidence_injective (d : ℕ) : Function.Injective (incidence d).mulVec := by
  intro y z he
  funext i
  have h := congrFun he (some i)
  simpa [incidence,Matrix.mulVec,dotProduct] using h

lemma actual_transpose_coordinate (d : ℕ) (x : Option (Fin d) → ZMod 2) (i : Fin d) :
    ((incidence d).transpose *ᵥ x) i = x (some i)+x none := by
  simp [incidence,Matrix.mulVec,dotProduct,Fintype.sum_option,add_comm]

/-- The exact transpose kernel is the constant line. This is the
nontrivial source of x=c*1 in the retained simultaneous descent argument. -/
theorem actual_incidence_transpose_kernel (d : ℕ) (x : Option (Fin d) → ZMod 2)
    (hx : (incidence d).transpose *ᵥ x=0) : ∀ i, x i=x none := by
  intro i
  cases i with
  | none => rfl
  | some i =>
    have h : x (some i)+x none=0 := by
      simpa only [actual_transpose_coordinate,Pi.zero_apply] using congrFun hx i
    exact add_right_cancel (h.trans (actual_two_add (x none)).symm)

end ActualTwoDescentIncidence318
