module
public import ActualTwoDescentReciprocalPrime318
public section
noncomputable section
namespace ActualTwoDescentZeroSumCompletion318
open scoped Matrix BigOperators
set_option maxHeartbeats 16000000

/-- Restore the deleted q0 row and column with zero row/column sums
in F2. Every original deleted-core entry is unchanged. -/
@[expose] def completion {ι : Type*} [Fintype ι]
    (A : Matrix ι ι (ZMod 2)) : Matrix (Option ι) (Option ι) (ZMod 2) :=
  fun i j => match i,j with
  | some i,some j => A i j
  | some i,none => ∑ j, A i j
  | none,some j => ∑ i, A i j
  | none,none => ∑ i, ∑ j, A i j

@[expose] def ones (ι : Type*) : ι → ZMod 2 := fun _ => 1

lemma actual_completion_coordinate {ι : Type*} [Fintype ι]
    (A : Matrix ι ι (ZMod 2)) (x : Option ι → ZMod 2) (i : ι) :
    (completion A *ᵥ x) (some i)=
      (A *ᵥ (fun j => x (some j)+x none)) i := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,completion,mul_add,
    Finset.sum_add_distrib,Finset.sum_mul]
  ring

/-- The restored matrix really kills the full constant vector. -/
lemma actual_completion_ones {ι : Type*} [Fintype ι]
    (A : Matrix ι ι (ZMod 2)) : completion A *ᵥ ones (Option ι)=0 := by
  funext i
  cases i with
  | some i =>
    rw [actual_completion_coordinate]
    simp only [ones,show (1 : ZMod 2)+1=0 by norm_num,Matrix.mulVec_zero,Pi.zero_apply]
  | none =>
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,completion,ones,mul_one]
    rw [Finset.sum_comm]
    exact ActualTwoDescentIncidence318.actual_two_add _

/-- A nonsingular deleted core gives EXACTLY the constant kernel on
the full support. The distinguished q0 coordinate supplies its scalar. -/
theorem actual_completion_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hA : IsUnit A)
    (x : Option ι → ZMod 2) (hx : completion A *ᵥ x=0) :
    x=x none • ones (Option ι) := by
  have hzero : A *ᵥ (fun j => x (some j)+x none)=0 := by
    funext i
    simpa only [actual_completion_coordinate,Pi.zero_apply] using congrFun hx (some i)
  have hv : (fun j => x (some j)+x none)=0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hA) (by simpa only [Matrix.mulVec_zero] using hzero)
  funext i
  cases i with
  | none => simp [ones]
  | some i =>
    have hh : x (some i)+x none=0 := congrFun hv i
    have he : x (some i)=x none :=
      add_right_cancel (hh.trans (ActualTwoDescentIncidence318.actual_two_add (x none)).symm)
    simpa only [Pi.smul_apply,ones,smul_eq_mul,mul_one] using he

end ActualTwoDescentZeroSumCompletion318
