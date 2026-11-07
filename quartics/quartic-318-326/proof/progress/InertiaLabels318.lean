module
public import Mathlib.Tactic
public section
noncomputable section
namespace InertiaLabels318
open Matrix
set_option maxHeartbeats 0

abbrev V := Fin 4→ZMod 2
@[expose] def labels:Matrix (Fin 4) (Fin 4) (ZMod 2):=
  !![1,1,1,0;1,1,0,1;1,0,1,1;0,1,1,1]
@[expose] def primes:Fin 4→ℕ:=![2,3,5,7]
@[expose] def divisor (v:V):ℕ:=∏j,if v j=0 then 1 else primes j

theorem labels_square : labels*labels=1 := by
  decide

theorem labels_symmetric : labels.transpose=labels := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Exact inverse of the labeled inertia coefficient map, over the actual F2. -/
theorem coefficient_map_involutive (v:V) : labels *ᵥ (labels *ᵥ v)=v := by
  rw [Matrix.mulVec_mulVec,labels_square,Matrix.one_mulVec]

theorem coefficient_map_injective : Function.Injective (fun v:V=>labels *ᵥ v) := by
  intro v w h
  have hh:=congrArg (fun x:V=>labels *ᵥ x) h
  simpa only [coefficient_map_involutive] using hh

theorem labels_combination (v:V) : (∑i,v i • labels i)=labels *ᵥ v := by
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  have hs:labels i j=labels j i := by
    have hh:=congrArg (fun M:Matrix (Fin 4) (Fin 4) (ZMod 2)=>M j i) labels_symmetric
    exact hh
  rw [hs,mul_comm]

/-- The four actual table labels are independent, not merely distinct. -/
theorem labels_independent (v:V) (h:∑i,v i • labels i=0) : v=0 := by
  rw [labels_combination] at h
  apply coefficient_map_injective
  simpa using h

theorem labels_span (x:V) : ∃v:V,∑i,v i • labels i=x := by
  refine ⟨labels *ᵥ x,?_⟩
  rw [labels_combination,coefficient_map_involutive]

/-- Multiplication of squareclasses is addition of their prime-exponent vectors. -/
theorem sum_labels : (∑i,labels i)=fun _=>1 := by
  decide

theorem literal_divisors :
    divisor (labels 0)=30 ∧ divisor (labels 1)=42 ∧
    divisor (labels 2)=70 ∧ divisor (labels 3)=105 ∧
    divisor (∑i,labels i)=210 := by
  decide

/-- The sphere's five-inertia relation forces the final label210 once the
four source rows are assigned, in the actual four-dimensional squareclass group. -/
theorem fifth_label (v:V) (h:(∑i,labels i)+v=0) : divisor v=210 := by
  have he:v=fun _=>1 := by
    ext j
    have hj:=congrFun h j
    rw [sum_labels] at hj
    simp only [Pi.add_apply,Pi.zero_apply] at hj
    have hv:v j= -1 := eq_neg_of_add_eq_zero_right hj
    have hn:(-1:ZMod 2)=1 := by decide
    exact hv.trans hn
  rw [he]
  decide

@[expose] def fiveLabels:Fin 5→V:=![labels 0,labels 1,labels 2,labels 3,fun _=>1]

theorem five_labels_injective : Function.Injective fiveLabels := by decide

theorem five_labels_nonzero : ∀i:Fin 5,fiveLabels i≠0 := by decide

theorem five_literal_divisors : ∀i:Fin 5,
    divisor (fiveLabels i)=(![30,42,70,105,210]:Fin 5→ℕ) i := by decide

/-- A permutation preserving each actual inertia label fixes every branch
index. This is the finite part of rationality under the Q-defined W action. -/
theorem labelled_permutation_fixed (sigma:Equiv.Perm (Fin 5))
    (h:∀i,fiveLabels (sigma i)=fiveLabels i) : sigma=1 := by
  apply Equiv.ext
  intro i
  exact five_labels_injective (h i)

end InertiaLabels318
